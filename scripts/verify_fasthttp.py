#!/usr/bin/env python3
"""Exercise the public handler API and its actual socket transport together."""
import contextlib
import json
import os
from pathlib import Path
import select
import socket
import subprocess
import time

from verify import connect, REQUEST

ROOT = Path(__file__).resolve().parents[1]


@contextlib.contextmanager
def server(executable, port):
    try:
        with connect(port):
            pass
    except ConnectionRefusedError:
        pass
    else:
        raise RuntimeError(f"port {port} already occupied")
    extra = []
    if os.environ.get("FASTHTTP_BACKEND") == "uv":
        executable = executable.with_name(executable.name.replace("lean-fast-http", "lean-uv-http"))
        extra = ["1"]
    p = subprocess.Popen(["taskset", "-c", os.environ.get("FASTHTTP_TEST_CPU", str(min(os.sched_getaffinity(0)))) , str(executable), str(port), *extra],
                         env={**os.environ, "LEAN_NUM_THREADS": "1"},
                         stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    try:
        for _ in range(100):
            assert p.poll() is None, p.stderr.read()
            try:
                with connect(port):
                    break
            except ConnectionRefusedError:
                time.sleep(.03)
        yield
        assert p.poll() is None, p.stderr.read()
    finally:
        p.terminate()
        try:
            _, errors = p.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            p.kill()
            _, errors = p.communicate(timeout=5)
        assert not errors, errors


def response(stream, body, status=b"200 OK", closing=False):
    assert stream.readline() == b"HTTP/1.1 " + status + b"\r\n"
    headers = {}
    while True:
        line = stream.readline()
        assert line, "unexpected EOF in response headers"
        if line == b"\r\n":
            break
        key, value = line.rstrip(b"\r\n").split(b":", 1)
        headers[key.lower()] = value.strip()
    assert int(headers[b"content-length"]) == len(body)
    assert headers[b"connection"] == (b"close" if closing else b"keep-alive")
    assert stream.read(len(body)) == body


def eof(sock):
    try:
        assert sock.recv(1) == b"", "rejected request unexpectedly dispatched"
    except ConnectionResetError:
        pass


def main():
    # The current API accepts bodies and returns explicit error responses.
    # The original GET-only checks are preserved with the baseline snapshot.
    from verify_fast_protocol import main as verify_current
    verify_current()


if __name__ == "__main__":
    main()
