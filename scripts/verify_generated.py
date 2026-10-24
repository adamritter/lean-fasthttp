#!/usr/bin/env python3
"""Exact-fragment tests of the executable parser, with independently generated
expected requests. No TCP coalescing can hide a fragmentation failure here."""
import argparse
import hashlib
import json
import ipaddress
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def fragments(wire, rng):
    out = [b'']
    while wire:
        n = rng.randint(1, min(len(wire), 73))
        out.append(wire[:n]); wire = wire[n:]
    return out + [b'']


def request(body=b'', chunked=False, target='/body', authority='localhost',
            method='POST', expect=False, close=False, minor=1, rng=None):
    rng = rng or random.Random(0)
    trailer = []
    head = f'{method} {target} HTTP/1.{minor}\r\nHost: localhost\r\n'.encode()
    if chunked:
        head += b'Transfer-Encoding: chunked\r\n'
        encoded = b''
        remaining = body
        while remaining:
            n = rng.randint(1, min(len(remaining), 127))
            extension = rng.choice([b'', b';a=b', b';flag', b';quote="a\\\"b"', b' ; a = "z"'])
            encoded += f'{n:X}'.encode() + extension + b'\r\n' + remaining[:n] + b'\r\n'
            remaining = remaining[n:]
        value = b'done\xff\x80'
        encoded += b'0\r\nX-Final: ' + value + b'\r\n\r\n'
        trailer = [['X-Final', value.hex()]]
    else:
        head += f'Content-Length: {len(body)}\r\n'.encode(); encoded = body
    if expect: head += b'Expect: 100-continue\r\n'
    if close: head += b'Connection: custom, CLOSE\r\n'
    path = target
    if '://' in target:
        authority, _, path = target.split('://', 1)[1].partition('/')
        path = '/' + path
    expected = dict(method=method, target=path, authority=authority, body=body.hex(),
        close=close or minor == 0, minor=minor, trailers=trailer)
    return head + b'\r\n' + encoded, expected, int(expect and minor != 0 and (chunked or bool(body)))


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--seed', type=int, default=20261024)
    p.add_argument('--cases', type=int, default=1000)
    p.add_argument('--probe', type=Path, default=ROOT / 'bin/protocol-probe')
    args = p.parse_args(); rng = random.Random(args.seed)
    inputs, expected, labels = [], [], []

    def add(chunks, requests, continues=0, error=0, limits=None, label='generated', raw_headers=None):
        case = {'chunks': [c.hex() for c in chunks]}
        if limits is not None: case['limits'] = limits
        inputs.append(case); expected.append(dict(requests=requests, continues=continues, error=error))
        labels.append(label)
        if raw_headers is not None: expected[-1]['raw_headers'] = [h.hex() for h in raw_headers]

    for i in range(args.cases):
        pipeline, requests, count = b'', [], 0
        for j in range(rng.randint(1, 4)):
            body = rng.randbytes(rng.choice([0, 1, 2, 17, 127, 256, 1024]))
            chunked = bool(rng.getrandbits(1))
            target = rng.choice(['/body', '/a%2Fb?x=1&y=%ff', 'http://other.example/body', 'https://[::1]:443/body'])
            wire, r, n = request(body, chunked, target, method=rng.choice(['GET','POST','PATCH','X-EXT']),
                expect=bool(rng.getrandbits(1)), rng=rng)
            pipeline += wire; requests.append(r); count += n
        add([pipeline], requests, count)
        add(fragments(pipeline, rng), requests, count, label='random-fragments')
        if i < 10:
            add([bytes([b]) for b in pipeline], requests, count, label='one-octet-fragments')

    # Exhaustively split fixed and chunked examples at every position, including
    # chunk metadata, body CRLF, the terminal chunk, trailers, and a pipeline.
    for chunked in (False, True):
        wire, r, n = request(b'a\x00b\xffc', chunked, expect=True)
        next_wire, r2, _ = request()
        wire += next_wire
        for i in range(len(wire) + 1):
            add([wire[:i], b'', wire[i:]], [r, r2], n, label='every-split')

    for minor in (0, 1, 9):
        wire, r, n = request(b'abc', minor=minor, close=True, expect=True)
        extra, _, _ = request(b'ignored')
        add(fragments(wire + extra, rng), [r], n, label='close-stops-pipeline')

    wire, r, _ = request(b'abc')
    head_size = wire.index(b'\r\n\r\n') + 4
    add(fragments(wire, rng), [r], limits=[head_size,3,1024,16384,65536], label='exact-limits')
    add([wire], [], error=431, limits=[head_size-1,3,1024,16384,65536], label='head-limit')
    add([wire], [], error=413, limits=[head_size,2,1024,16384,65536], label='body-limit')

    invalid = [
        (b'GET / HTTP/1.1\r\n\r\n', 400),
        (b'GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n', 400),
        (b'POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\n', 400),
        (b'GET / HTTP/2.0\r\nHost: a\r\n\r\n', 505),
    ]
    for name in [b'Bad Name', b'Bad\x00Name', b' folded', b'Bad\x7fName']:
        invalid.append((b'GET / HTTP/1.1\r\nHost: a\r\n'+name+b': x\r\n\r\n', 400))
    for length in [b'+1', b'-1', b'1,2', b'1x', b'', b'999999999999999999999999999999']:
        invalid.append((b'POST / HTTP/1.1\r\nHost: a\r\nContent-Length: '+length+b'\r\n\r\n', 413 if length.startswith(b'999') else 400))
    for wire, status in invalid:
        add([wire], [], error=status, label='malformed')
        add([bytes([b]) for b in wire], [], error=status, label='malformed-fragments')

    # Independent ipaddress generation exercises compressed and expanded IPv6,
    # IPv4 tails, percent escapes, empty/large ports, and malformed authorities.
    for i in range(500):
        ip = ipaddress.IPv6Address(rng.getrandbits(128) if i % 2 else rng.getrandbits(48))
        host = '[' + (ip.compressed if i % 3 else ip.exploded) + ']:' + str(rng.randrange(100000))
        wire, r, _ = request()
        wire = wire.replace(b'Host: localhost', b'Host: ' + host.encode())
        r['authority'] = host
        add(fragments(wire, rng), [r], label='independent-ipv6')
        for bad in [host + ':1', host.replace('[', '[z', 1)]:
            add([wire.replace(host.encode(), bad.encode())], [], error=400, label='invalid-ipv6')
    for host in ['a%3ab:80', 'a%2Fb:', 'a!$&()*+,;=b:999999999999999999999999',
            '[::ffff:192.0.2.1]', '[v1.a:b]', '', 'localhost:']:
        wire, r, _ = request(); wire = wire.replace(b'Host: localhost', b'Host: ' + host.encode())
        r['authority'] = host; add(fragments(wire, rng), [r], label='authority-boundaries')

    # Exercise the entire octet alphabet for field values, including obs-text.
    for b in range(256):
        wire, r, _ = request()
        wire = wire.replace(b'Host: localhost\r\n', b'Host: localhost\r\nX: ' + bytes([b]) + b'\r\n')
        valid = b == 9 or (b >= 32 and b != 127)
        add(fragments(wire, rng), [r] if valid else [], error=0 if valid else 400, label='all-field-value-octets')

    # The configured count limits data chunks, not the mandatory terminal chunk.
    prefix = b'POST /body HTTP/1.1\r\nHost: localhost\r\nTransfer-Encoding: chunked\r\n\r\n'
    _, empty, _ = request(); empty['trailers'] = []
    add([prefix + b'0\r\n\r\n'], [empty], limits=[16384,1024,1024,16384,0], label='zero-data-chunks')
    one = {**empty, 'body': b'x'.hex()}
    add([prefix + b'1\r\nx\r\n0\r\n\r\n'], [one], limits=[16384,1,1024,16384,1], label='exact-chunk-limit')
    add([prefix + b'1\r\nx\r\n1\r\ny\r\n0\r\n\r\n'], [], error=413,
        limits=[16384,1024,1024,16384,1], label='chunk-limit-exceeded')
    for line in [b'1;flag ', b'1;key=x ', b'1;key="x" ', b'1 ; ', b'1;key="x\x7f"']:
        add([prefix + line + b'\r\nx\r\n0\r\n\r\n'], [], error=400, label='invalid-chunk-extensions')
    wire, r, _ = request(b'abc')
    for i in range(len(wire) + 3):
        leading = b'\r\n' + wire
        add([leading[:i], leading[i:]], [r], label='leading-crlf-splits')

    for coding in [b'chunked', b', chunked,', b',\r\nTransfer-Encoding: chunked',
            b'chunked\r\nTransfer-Encoding: ,']:
        wire = prefix.replace(b'chunked', coding) + b'0\r\n\r\n'
        add(fragments(wire, rng), [empty], label='combined-transfer-coding-fields')
    for coding, status in [(b'gzip\r\nTransfer-Encoding: chunked', 501),
            (b'chunked\r\nTransfer-Encoding: gzip',400), (b'chunked, chunked',400),
            (b'gzip;key="a,b", chunked',501), (b'gzip;key, chunked',400)]:
        add(fragments(prefix.replace(b'chunked', coding), rng), [], error=status, label='transfer-coding-order')
    for target, status in [('urn:isbn:123',501), ('file:///tmp/example',501),
            ('ftp://user:pass@example.org/file',501), ('1urn:value',400), ('urn:bad%zz',400)]:
        wire, _, _ = request(target=target)
        add(fragments(wire, rng), [], error=status, label='absolute-uri-scheme')

    # A one-octet extension method and headerless HTTP/1.0 form a valid
    # 16-octet request. GET-only minimum-length assumptions must not reject it.
    for method in "!#$%&'*+-.^_`|~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz":
        wire = method.encode() + b' / HTTP/1.0\r\n\r\n'
        r = dict(method=method, target='/', authority='', body='', close=True, minor=0, trailers=[])
        for split in range(len(wire)+1):
            add([wire[:split], wire[split:]], [r], label='minimal-http10-method')

    # Independent lexical regressions: all possible percent-escape octets,
    # and decimal values with leading zeros around independently chosen limits.
    for byte in range(256):
        target = b'/a%' + bytes([byte]) + b'0'
        wire, expected_request, _ = request()
        wire = wire.replace(b'/body', target)
        valid = byte in b'0123456789abcdefABCDEF'
        if valid: expected_request['target'] = target.decode('ascii')
        add(fragments(wire, rng), [expected_request] if valid else [],
            error=0 if valid else 400, label='percent-escape-octets')
    for _ in range(256):
        n = rng.randrange(257)
        limit = rng.randrange(257)
        body = rng.randbytes(n)
        wire, r, _ = request(body)
        wire = wire.replace(b'Content-Length: ' + str(n).encode(),
            b'Content-Length: ' + b'0' * rng.randrange(1,33) + str(n).encode())
        add(fragments(wire, rng), [r] if n <= limit else [],
            error=0 if n <= limit else 413, limits=[16384,limit,1024,16384,65536],
            label='bounded-decimal-leading-zeros')

    # Full raw-header equality across header/body/pipeline splits. Previously
    # Request.raw exposed different body/pipeline suffixes for different receives.
    for chunked in [False, True]:
        for expect in [False, True]:
            first, r1, continues = request(b'body\x00\xff\r\n\r\n', chunked=chunked, expect=expect)
            second, r2, _ = request(b'next', target='/next')
            wire = first + second
            raw = [first.split(b'\r\n\r\n',1)[0] + b'\r\n\r\n',
                second.split(b'\r\n\r\n',1)[0] + b'\r\n\r\n']
            for split in range(len(wire)+1):
                add([wire[:split], wire[split:]], [r1,r2], continues,
                    label='raw-header-and-pipeline-fragmentation', raw_headers=raw)
    # A limit rejection must not inspect unconsumed future bytes to decide
    # between 431 and 414. An eight-byte limit precedes the long target.
    wire = b'GET /' + b'x'*10000 + b' HTTP/1.1\r\nHost: localhost\r\n\r\n'
    for split in [0,1,7,8,9,10,9000,len(wire)]:
        add([wire[:split], wire[split:]], [], error=431,
            limits=[8,1048576,1024,16384,65536], label='limit-error-fragmentation')

    tokens = b"!#$%&'*+-.^_`|~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    for byte in range(256):
        wire, r, _ = request()
        method = b'X' + bytes([byte])
        wire = wire.replace(b'POST ', method + b' ', 1)
        valid = byte in tokens
        if valid: r['method'] = method.decode('ascii')
        add(fragments(wire,rng), [r] if valid else [], error=0 if valid else 400,
            label='all-method-octets')
        wire, r, _ = request()
        wire = wire.replace(b'Host: localhost\r\n', b'Host: localhost\r\nX' + bytes([byte]) + b': z\r\n')
        valid = byte in tokens or byte == 58
        add(fragments(wire,rng), [r] if valid else [], error=0 if valid else 400,
            label='all-field-name-octets')

    for _ in range(256):
        n = rng.randrange(257)
        limit = rng.randrange(257)
        body = rng.randbytes(n)
        wire, r, _ = request(body, chunked=True, rng=rng)
        add(fragments(wire,rng), [r] if n <= limit else [],
            error=0 if n <= limit else 413, limits=[16384,limit,1024,16384,65536],
            label='chunked-cumulative-body-budget')
        _, r, _ = request(body)
        wire = b'POST /body HTTP/1.1\r\nHost: localhost\r\nTransfer-Encoding: chunked\r\n\r\n'
        if n:
            wire += b'0' * rng.randrange(1,33) + f'{n:X}'.encode() + b'\r\n' + body + b'\r\n'
        wire += b'0000\r\n\r\n'
        add(fragments(wire,rng), [r] if n <= limit else [],
            error=0 if n <= limit else 413, limits=[16384,limit,1024,16384,65536],
            label='hexadecimal-leading-zeros-budget')

    payload = ''.join(json.dumps(case) + '\n' for case in inputs).encode()
    run = subprocess.run([str(args.probe)], input=payload, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    assert run.returncode == 0, run.stderr.decode()
    lines = run.stdout.splitlines()
    assert len(lines) == len(inputs), (len(lines), len(inputs), run.stderr)
    for i, (line, want) in enumerate(zip(lines, expected)):
        got = json.loads(line)
        for key, value in want.items():
            assert got[key] == value, (i, labels[i], key, got, want, inputs[i])
        if not want['error']:
            assert got['pending'] == 'idle', (i, got)
    print(json.dumps({'result':'PASS', 'seed':args.seed, 'generated_pipelines':args.cases,
        'exact_fragment_cases':len(inputs), 'input_sha256':hashlib.sha256(payload).hexdigest(),
        'probe_sha256':hashlib.sha256(args.probe.read_bytes()).hexdigest(),
        'case_classes':{label:labels.count(label) for label in sorted(set(labels))}}, indent=2))

if __name__ == '__main__':
    main()
