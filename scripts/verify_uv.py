#!/usr/bin/env python3
"""Fresh multi-worker HTTP integration tests using the complete public handler API."""
import concurrent.futures
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import random
import signal
import socket
import subprocess
import time
from verify_fast_protocol import req, receive

ROOT = Path(__file__).resolve().parents[1]


def main():
    seed = int.from_bytes(os.urandom(8), 'big')
    rng = random.Random(seed)
    cpus = sorted(os.sched_getaffinity(0))[:4]
    # CI may expose fewer than four CPUs; still exercise four distinct I/O loops.
    binary = ROOT / 'bin/lean-uv-http-example'
    with socket.socket() as reservation:
        reservation.bind(('127.0.0.1', 0))
        port = reservation.getsockname()[1]
    address = ('127.0.0.1', port)
    process = subprocess.Popen(['taskset', '-c', ','.join(map(str, cpus)), str(binary), str(port), '4'],
        env={**os.environ, 'LEAN_NUM_THREADS': '1'}, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    workers = set()
    stream_counts = Counter()
    cleanup_checks = 0
    inputs = [rng.randbytes(rng.randrange(1, 8193)) for _ in range(160)]
    try:
        for attempt in range(300):
            assert process.poll() is None, process.communicate()
            try:
                with socket.create_connection(address, .1):
                    break
            except OSError:
                time.sleep(.01)
        else:
            raise AssertionError('startup timeout')

        def exchange(case):
            i, body = case
            local = random.Random(seed + i)
            # Every connection has a body, a deferred reply, a second body, and
            # a final close response. Ordering must survive promise suspension.
            chunked = (f'{len(body):x};id={i}\r\n'.encode() + body + b'\r\n0\r\nX-End: yes\r\n\r\n')
            wire = (req('POST', '/body', f'Content-Length: {len(body)}\r\n'.encode(), body)
                    + req('GET', '/deferred', b'X-Value: ' + body.hex()[:24].encode() + b'\r\n')
                    + req('POST', '/body', b'Transfer-Encoding: chunked\r\n', chunked)
                    + req('POST', '/stream-body', f'Content-Length: {len(body)}\r\n'.encode(), body)
                    + req('HEAD', '/', b'Connection: close\r\n') + req('GET', '/fail'))
            with socket.create_connection(address, 5) as sock, sock.makefile('rb') as stream:
                sock.sendall(req('GET', '/worker'))
                assert stream.readline().startswith(b'HTTP/1.1 200 ')
                headers = {}
                while (line := stream.readline()) != b'\r\n':
                    assert line
                    k, v = line.rstrip(b'\r\n').split(b':', 1)
                    headers[k.lower()] = v.strip()
                worker = int(stream.read(int(headers[b'content-length'])))
                offset = 0
                while offset < len(wire):
                    n = local.randrange(1, 2049)
                    sock.sendall(wire[offset:offset+n])
                    offset += n
                sock.shutdown(socket.SHUT_WR)
                receive(stream, body)
                receive(stream, body.hex()[:24].encode())
                receive(stream, body)
                assert stream.readline().startswith(b'HTTP/1.1 200 ')
                stream_headers = {}
                while (line := stream.readline()) != b'\r\n':
                    assert line
                    key, value = line.rstrip(b'\r\n').split(b':',1)
                    stream_headers[key.lower()] = value.strip()
                assert stream_headers[b'transfer-encoding'] == b'chunked'
                decoded = bytearray()
                while True:
                    line = stream.readline()
                    assert line.endswith(b'\r\n')
                    count = int(line[:-2],16)
                    if count == 0:
                        assert stream.read(2) == b'\r\n'
                        break
                    chunk = stream.read(count)
                    assert len(chunk) == count and stream.read(2) == b'\r\n'
                    decoded += chunk
                assert decoded == body
                receive(stream, head=True)
                assert stream.read(1) == b'', 'close must discard the pipelined /fail'
                return worker

        with concurrent.futures.ThreadPoolExecutor(32) as pool:
            stream_counts.update(pool.map(exchange, enumerate(inputs)))
            workers.update(stream_counts)
        assert workers == {0, 1, 2, 3}, workers
        # Query every worker on the same connection used to identify it. Each
        # completed dynamic stream must have released its producer exactly once.
        checked_workers = set()
        for _ in range(128):
            with socket.create_connection(address,5) as sock, sock.makefile('rb') as stream:
                sock.sendall(req('GET','/worker') + req('GET','/released',b'Connection: close\r\n'))
                assert stream.readline().startswith(b'HTTP/1.1 200 ')
                headers = {}
                while (line := stream.readline()) != b'\r\n':
                    assert line
                    key,value = line.rstrip(b'\r\n').split(b':',1)
                    headers[key.lower()] = value.strip()
                worker = int(stream.read(int(headers[b'content-length'])))
                receive(stream, str(stream_counts[worker]).encode())
                assert stream.read(1) == b''
                cleanup_checks += 1
                checked_workers.add(worker)
                if checked_workers == workers: break
        assert checked_workers == workers
        # Close while a promise is pending; callback state must be reclaimed,
        # and independent clients must continue to receive correct responses.
        for _ in range(32):
            with socket.create_connection(address, 5) as sock:
                sock.sendall(req('GET', '/deferred'))
        time.sleep(.3)
        with socket.create_connection(address, 5) as sock, sock.makefile('rb') as stream:
            sock.sendall(req('GET', '/', b'Connection: close\r\n'))
            receive(stream)
            assert stream.read(1) == b''
    finally:
        process.send_signal(signal.SIGTERM)
        out, err = process.communicate(timeout=10)
        assert process.returncode == 0 and not err, (process.returncode, out, err)
    print(json.dumps({'result': 'PASS', 'seed': seed, 'workers': sorted(workers),
        'server_cpus': cpus, 'connections': len(inputs), 'checked_responses': 160*6+1+cleanup_checks*2,
        'completed_streams_by_worker':dict(sorted(stream_counts.items())),
        'cleanup_check_connections':cleanup_checks,
        'request_semantics': 'fixed, chunked, deferred, dynamic streaming, per-worker exactly-once cleanup, HEAD, close, half-close, pipeline ordering',
        'input_sha256': hashlib.sha256(b''.join(inputs)).hexdigest(),
        'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
