#!/usr/bin/env python3
"""Independent wire regressions for RFC 9112 targets, authority, and framing."""
import json
from verify import connect
from verify_fasthttp import ROOT, server
from verify_fast_protocol import PORT, req, exchange, receive, reject


def main():
    valid_hosts = [b'localhost', b'example.org:8080', b'[::1]:443',
        b'[2001:db8::192.0.2.1]', b'[1:2:3:4:5:6:7:8]', b'[vF.a:b]', b'', b'example.org:']
    invalid_hosts = [b'bad host', b'user@host', b'host/path', b'host#frag', b'host?query',
        b'[:::1]', b'[1:2:3:4:5:6:7]', b'[1:2:3:4:5:6:7:8:9]', b'[1:2:3:4:5:6:7:8::]',
        b'[::ffff:192.00.2.1]', b'[::ffff:256.1.2.3]', b'[::1', b'::1', b'host:port',
        b'host:12:34', b'%zz', b'[v.a]', b'[v1.]', b'[::1]junk', b'\\host']
    with server(ROOT / 'bin/lean-fast-http-example', PORT):
        for host in valid_hosts:
            exchange(b'GET /authority HTTP/1.1\r\nHost: ' + host + b'\r\n\r\n', host)
        for host in invalid_hosts:
            reject(b'GET / HTTP/1.1\r\nHost: ' + host + b'\r\n\r\n')
        for authority in ['example.org', '[::1]:80', 'localhost:8080']:
            wire = req(target='http://' + authority + '/authority')
            exchange(wire, authority.encode())
            with connect(PORT) as s, s.makefile('rb') as f:
                for split in range(1, len(wire)):
                    s.sendall(wire[:split]); s.sendall(wire[split:] + req())
                    receive(f, authority.encode()); receive(f)
        for target in ['http://example.org', 'HTTP://example.org/', 'https://example.org/']:
            exchange(req(target=target))
        exchange(req(target='http://example.org/request-target'), b'http://example.org/request-target')
        for target in ['/a%20b?x=%ff&y=1', '/a:b@c!$&\'()*+,;=', '/?q=/?:@']:
            exchange(req(target=target))
        for target in ['/back\\slash', '/[bad]', '/{bad}', '/bad|path', '/bad^path',
                '/bad`path', '/bad%a', '/bad%gg', 'http://', 'http://:80/',
                'http://user@example.org/', 'http://example.org/#fragment', 'http://[:::1]/']:
            reject(req(target=target))
        for conn in [b'keep-alive, close', b', , CLOSE,', b'custom-token, close']:
            with connect(PORT) as s, s.makefile('rb') as f:
                s.sendall(req(headers=b'Connection: '+conn+b'\r\n') + req())
                assert receive(f)[b'connection'] == [b'close']
                assert f.read(1) == b''
        for conn in [b'close garbage', b'"close"', b'close;foo']:
            reject(req(headers=b'Connection: '+conn+b'\r\n'))
        exchange(req('POST', '/raw-trailers', b'Transfer-Encoding: chunked\r\n',
            b'0\r\nX-Final: \xff\x80\r\n\r\n'), b'\xff\x80')
        reject(b'CONNECT example.com:443 HTTP/1.1\r\n\r\n')
        reject(req('CONNECT', 'example.com:443'), 501)
        reject(req('CONNECT', 'example.com'))
        reject(req('CONNECT', 'example.com:'))
        reject(req().replace(b'HTTP/1.1', b'HTTP/2.0'), 505)
        exchange(req().replace(b'HTTP/1.1', b'HTTP/1.9'))
        exchange(req(headers=b'Upgrade: websocket\r\nConnection: Upgrade\r\n'))
    print(json.dumps({'result': 'PASS', 'host_valid': len(valid_hosts),
        'host_invalid': len(invalid_hosts), 'absolute_targets_and_authority': 'PASS',
        'uri_octet_grammar_connection_lists_binary_trailers_versions': 'PASS'}, indent=2))

if __name__ == '__main__':
    main()
