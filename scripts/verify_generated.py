#!/usr/bin/env python3
"""Exact-fragment tests of the executable parser, with independently generated
expected requests. No TCP coalescing can hide a fragmentation failure here."""
import argparse
import hashlib
import json
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

    def add(chunks, requests, continues=0, error=0, limits=None, label='generated'):
        case = {'chunks': [c.hex() for c in chunks]}
        if limits is not None: case['limits'] = limits
        inputs.append(case); expected.append(dict(requests=requests, continues=continues, error=error))
        labels.append(label)

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
