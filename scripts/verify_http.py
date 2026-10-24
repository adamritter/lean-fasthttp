#!/usr/bin/env python3
"""Semantic HTTP checks for Std.Http (header order/casing can differ)."""
import concurrent.futures
import socket
import sys
import time
from verify import BODY, REQUEST, connect


class Client:
    def __init__(self, port):
        self.sock = connect(port)
        self.reader = self.sock.makefile("rb")

    def close(self):
        self.reader.close()
        self.sock.close()

    def receive(self):
        status = self.reader.readline()
        assert status.split()[:2] == [b"HTTP/1.1", b"200"], status
        headers = {}
        while True:
            line = self.reader.readline()
            assert line, "unexpected EOF in headers"
            if line == b"\r\n":
                break
            k, v = line.split(b":", 1)
            headers[k.lower()] = v.strip()
        assert headers.get(b"content-length") == b"1024", headers
        assert headers.get(b"content-type") == b"application/octet-stream", headers
        assert self.reader.read(1024) == BODY


def verify_http(port):
    c = Client(port)
    try:
        for _ in range(150):
            c.sock.sendall(REQUEST)
            c.receive()
        for split in range(1, len(REQUEST)):
            c.sock.sendall(REQUEST[:split])
            time.sleep(0.001)
            c.sock.sendall(REQUEST[split:])
            c.receive()
        c.sock.sendall(REQUEST * 128)
        time.sleep(0.03)
        for _ in range(128):
            c.receive()
    finally:
        c.close()

    def client(_):
        c = Client(port)
        try:
            for _ in range(20):
                c.sock.sendall(REQUEST)
                c.receive()
        finally:
            c.close()

    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool:
        list(pool.map(client, range(32)))
    # The full HTTP server also honors Connection: close.
    c = Client(port)
    try:
        c.sock.sendall(b"GET / HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n")
        c.receive()
        assert c.reader.read(1) == b""
    finally:
        c.close()
    return "PASS: 200, exact 1024-byte body, Content-Length/Type, 150 keep-alive requests, all splits, 128 pipelined responses, concurrent clients, Connection: close"


if __name__ == "__main__":
    print(verify_http(int(sys.argv[1])))
