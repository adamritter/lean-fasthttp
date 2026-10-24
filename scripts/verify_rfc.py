#!/usr/bin/env python3
"""Independent wire regressions for RFC 9112 targets, authority, and framing."""
import json
import time
from email.utils import parsedate_to_datetime
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
        exchange(b'\r\n' + req())
        exchange(req('POST', '/body', b'Transfer-Encoding: , CHUNKED, ,\r\n', b'0\r\n\r\n'), b'')
        reject(req(headers=b'Transfer-Encoding: gzip;key="a,b", chunked\r\n'), 501)
        reject(req(headers=b'Transfer-Encoding: gzip\r\nTransfer-Encoding: chunked\r\n'), 501)
        exchange(req('POST', '/body', b'Transfer-Encoding: ,\r\nTransfer-Encoding: chunked\r\n', b'0\r\n\r\n'), b'')
        for target in ['urn:isbn:123', 'file:///tmp/example', 'ftp://user:pass@example.org/file']:
            reject(req(target=target), 501)
        for target in ['1urn:value', 'urn:bad%zz', 'ftp://[:::1]/file']:
            reject(req(target=target))
        reject(req(headers=b'Transfer-Encoding: gzip, chunked\r\nContent-Length: 0\r\n'))
        for coding in [b'chunked, gzip', b'chunked, chunked', b'gzip', b'chunked;foo=bar', b'gzip;foo, chunked']:
            reject(req(headers=b'Transfer-Encoding: ' + coding + b'\r\n'))
        reject(req(target='/' + 'x' * 17000), 414)
        first = exchange(req())[b'date']
        time.sleep(1.1)
        second = exchange(req())[b'date']
        assert len(first) == len(second) == 1 and first != second
        for value in first + second:
            assert value.endswith(b' GMT')
            assert abs(parsedate_to_datetime(value.decode()).timestamp() - time.time()) < 4
        assert b'date' in exchange(req('GET', '/status/204'), b'hidden', 204)
        assert b'date' in exchange(req('GET', '/status/304'), b'hidden', 304)
        # HTTP/1.0 has no chunked coding or implicit persistence. A streamed
        # body is delimited by EOF; a HEAD stream must not invoke the producer.
        for target, expected, is_head in [('/', b'ready', False), ('/stream', b's' * 8388608, False),
                ('/stream', b'', True)]:
            with connect(PORT) as s, s.makefile('rb') as f:
                s.settimeout(20)
                method = 'HEAD' if is_head else 'GET'
                s.sendall(f'{method} {target} HTTP/1.0\r\n\r\n'.encode())
                assert f.readline().startswith(b'HTTP/1.0 200 ')
                headers = {}
                while (line := f.readline()) != b'\r\n':
                    assert line
                    k, v = line.split(b':', 1); headers[k.lower()] = v.strip()
                assert headers[b'connection'] == b'close' and b'date' in headers
                assert b'transfer-encoding' not in headers
                assert f.read() == expected
        with connect(PORT) as s, s.makefile('rb') as f:
            s.sendall(b'POST /body HTTP/1.0\r\nContent-Length: 3\r\nExpect: 100-continue\r\n\r\nabc')
            assert f.readline().startswith(b'HTTP/1.0 200 ')
            assert f.read().endswith(b'\r\n\r\nabc')
        reject(b'POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n')
    print(json.dumps({'result': 'PASS', 'host_valid': len(valid_hosts),
        'host_invalid': len(invalid_hosts), 'absolute_targets_and_authority': 'PASS',
        'uri_octet_grammar_connection_lists_binary_trailers_versions': 'PASS',
        'date_freshness_and_http10_fixed_stream_head': 'PASS'}, indent=2))

if __name__ == '__main__':
    main()
