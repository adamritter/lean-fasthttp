#!/usr/bin/env python3
"""Wire-level checks for the intentionally small bodyless HTTP/1.1 protocol."""
import concurrent.futures
import socket
import sys
import time

REQUEST = b"GET / HTTP/1.1\r\nHost: localhost\r\n\r\n"
BODY = b"x" * 1024
RESPONSE = (b"HTTP/1.1 200 OK\r\nContent-Length: 1024\r\n"
            b"Content-Type: application/octet-stream\r\n"
            b"Connection: keep-alive\r\n\r\n" + BODY)


def connect(port):
    return socket.create_connection(("127.0.0.1", port), timeout=5)


def receive(sock, n=1):
    expected = RESPONSE * n
    data = bytearray()
    while len(data) < len(expected):
        part = sock.recv(len(expected) - len(data))
        assert part, f"unexpected EOF at {len(data)}/{len(expected)} bytes"
        data.extend(part)
    assert data == expected, "response status, headers or body mismatch"


def verify(port):
    with connect(port) as s:
        for _ in range(100):
            s.sendall(REQUEST)
            receive(s)
    # Split at EVERY position, including every byte of CRLFCRLF.
    with connect(port) as s:
        for split in range(1, len(REQUEST)):
            s.sendall(REQUEST[:split])
            time.sleep(0.001)
            s.sendall(REQUEST[split:])
            receive(s)
    with connect(port) as s:
        s.sendall(REQUEST * 128)
        time.sleep(0.03)  # delayed reader
        receive(s, 128)
    # Exact header-size boundary, split across several receive buffers.
    prefix = b"GET / HTTP/1.1\r\nX-Pad: "
    with connect(port) as s:
        s.sendall(prefix + b"a" * (16384 - len(prefix) - 4) + b"\r\n\r\n")
        receive(s)
        s.sendall(REQUEST)
        receive(s)
    # Completing an overlong header must not reset away the error flag.
    with connect(port) as s:
        s.sendall(prefix + b"a" * (16385 - len(prefix) - 4) + b"\r\n\r\n")
        try:
            assert s.recv(1) == b""
        except ConnectionResetError:
            pass
    with connect(port) as s:
        s.sendall(REQUEST * 8)
        s.shutdown(socket.SHUT_WR)
        receive(s, 8)
        assert s.recv(1) == b"", "EOF must close after pending responses"
    # Too much header data is rejected without a response.
    with connect(port) as s:
        s.sendall(b"GET / HTTP/1.1\r\nX-Large: " + b"a" * 17000)
        try:
            assert s.recv(1) == b""
        except ConnectionResetError:
            pass
    def client(_):
        with connect(port) as s:
            for _ in range(20):
                s.sendall(REQUEST)
                receive(s)
    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool:
        list(pool.map(client, range(32)))
    # Abrupt disconnect must not kill the process (SIGPIPE).
    for _ in range(10):
        with connect(port) as s:
            s.sendall(REQUEST * 64)
    client(0)
    return "PASS: exact 1024-byte body, keep-alive, all request splits, pipeline, half-close, header limit, concurrent clients, disconnects"


if __name__ == "__main__":
    print(verify(int(sys.argv[1])))
