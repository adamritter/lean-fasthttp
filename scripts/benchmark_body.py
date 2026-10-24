#!/usr/bin/env python3
"""Single-connection body/echo regression, separate from GET requests/s measurements.
Client verifies every response; a Python client can limit absolute throughput.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--binaries', nargs='+', default=['bin/lean-uv-http-example'])
    ap.add_argument('--requests', type=int, default=200)
    ap.add_argument('--repeats', type=int, default=3)
    ap.add_argument('--server-cpu', type=int, default=16)
    ap.add_argument('--client-cpu', type=int, default=24)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert args.server_cpu != args.client_cpu and not args.output.exists()
    os.sched_setaffinity(0, {args.client_cpu})
    body = bytes(range(256)) * 4096
    cases = {
        'fixed': b'POST /body HTTP/1.1\r\nHost: localhost\r\nContent-Length: 1048576\r\n\r\n' + body,
        'chunked': b'POST /body HTTP/1.1\r\nHost: localhost\r\nTransfer-Encoding: chunked\r\n\r\n'
            + b'100000\r\n' + body + b'\r\n0\r\n\r\n'}
    rows = []
    for repeat in range(args.repeats):
        binaries = args.binaries if repeat % 2 == 0 else list(reversed(args.binaries))
        for name in binaries:
            binary = ROOT / name
            with socket.socket() as reservation:
                reservation.bind(('127.0.0.1', 0))
                port = reservation.getsockname()[1]
            proc = subprocess.Popen(['taskset', '-c', str(args.server_cpu), str(binary), str(port), '1'],
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, env={**os.environ, 'LEAN_NUM_THREADS': '1'})
            try:
                for _ in range(300):
                    assert proc.poll() is None, proc.communicate()
                    try:
                        sock = socket.create_connection(('127.0.0.1', port), 5)
                        break
                    except OSError:
                        time.sleep(.01)
                else:
                    raise AssertionError('startup timeout')
                with sock, sock.makefile('rb') as stream:
                    for framing, wire in cases.items():
                        def exchange():
                            sock.sendall(wire)
                            assert stream.readline().startswith(b'HTTP/1.1 200 ')
                            headers = {}
                            while (line := stream.readline()) != b'\r\n':
                                assert line
                                key, value = line.rstrip(b'\r\n').split(b':', 1)
                                headers[key.lower()] = value.strip()
                            assert headers[b'content-length'] == b'1048576'
                            assert stream.read(len(body)) == body
                        for _ in range(10): exchange()
                        start = time.monotonic()
                        for _ in range(args.requests): exchange()
                        elapsed = time.monotonic() - start
                        row = {'binary': name, 'sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
                            'framing': framing, 'repeat': repeat+1, 'seconds': elapsed,
                            'MiB_per_second': args.requests/elapsed, 'requests': args.requests,
                            'body_bytes': len(body), 'verified': True}
                        rows.append(row)
                        print(f'{name} {framing}: {row["MiB_per_second"]:.1f} MiB/s', flush=True)
            finally:
                proc.terminate()
                _, err = proc.communicate(timeout=10)
                assert proc.returncode == 0 and not err, (proc.returncode, err)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({'metric': 'single-client loopback echo body MiB/s',
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'server_cpu': args.server_cpu, 'client_cpu': args.client_cpu,
        'limitation': 'Python validation and echo transport are included; not an isolated parser benchmark',
        'runs': rows}, indent=2)+'\n')


if __name__ == '__main__':
    main()
