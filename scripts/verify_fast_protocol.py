#!/usr/bin/env python3
"""Adversarial wire tests for the expanded callback server; no H1 dependency."""
import concurrent.futures
import json
import random
import select
import socket
import time
from verify import connect, REQUEST
from verify_fasthttp import server, ROOT
from verify_http import verify_http

PORT = 18096

def req(method='GET', target='/', headers=b'', body=b''):
    return f'{method} {target} HTTP/1.1\r\nHost: localhost\r\n'.encode()+headers+b'\r\n'+body

def receive(f, body=b'ready', status=200, head=False):
    line=f.readline()
    assert line.startswith(f'HTTP/1.1 {status} '.encode()), line
    headers={}
    while True:
        line=f.readline()
        assert line, 'EOF in headers'
        if line==b'\r\n': break
        k,v=line.rstrip(b'\r\n').split(b':',1)
        headers.setdefault(k.lower(),[]).append(v.strip())
    if status==204:
        assert b'content-length' not in headers
    elif status==205:
        assert headers[b'content-length']==[b'0']
    else:
        assert headers[b'content-length']==[str(len(body)).encode()], headers
    if not head and status not in (204,205,304):
        assert f.read(len(body))==body
    return headers

def exchange(request, body=b'ready', status=200):
    with connect(PORT) as s, s.makefile('rb') as f:
        s.sendall(request)
        return receive(f,body,status)

def reject(request,status=400):
    with connect(PORT) as s,s.makefile('rb') as f:
        s.sendall(request+req())
        headers=receive(f,b'',status)
        assert headers[b'connection']==[b'close']
        try: assert f.read(1)==b''
        except ConnectionResetError: pass

def main():
    results={}
    with server(ROOT/'bin/lean-fast-http',18095):
        results['static']=verify_http(18095)
    with server(ROOT/'bin/lean-fast-http-example',PORT):
        # Producer resources must be released exactly once on completion,
        # HEAD suppression, and producer failure after headers were sent.
        def stream_head(f):
            assert f.readline().startswith(b'HTTP/1.1 200 ')
            lines=[]
            while True:
                line=f.readline(); assert line
                if line==b'\r\n': break
                lines.append(line.lower())
            assert b'transfer-encoding: chunked\r\n' in lines
        with connect(PORT) as s,s.makefile('rb') as f:
            s.settimeout(20)
            s.sendall(req(target='/stream')+req()); time.sleep(.1)
            stream_head(f)
            for _ in range(128):
                assert f.readline()==b'10000\r\n'
                assert f.read(65536)==b's'*65536
                assert f.read(2)==b'\r\n'
            assert f.read(5)==b'0\r\n\r\n'; receive(f)
        exchange(req(target='/released'),b'1')
        with connect(PORT) as s,s.makefile('rb') as f:
            s.sendall(req('HEAD','/stream')+req()); stream_head(f); receive(f)
        exchange(req(target='/released'),b'2')
        with connect(PORT) as s,s.makefile('rb') as f:
            s.sendall(req(target='/stream-error')+req()); stream_head(f)
            assert f.readline()==b'10000\r\n'; assert f.read(65536)==b's'*65536
            assert f.read(2)==b'\r\n'; assert f.read(1)==b''
        exchange(req(target='/released'),b'3')
        for method in ['GET','POST','PUT','PATCH','DELETE','OPTIONS','CUSTOM']:
            exchange(req(method,'/method'),method.encode())
        exchange(req('OPTIONS','*'))
        exchange(req(headers=b'Connection: upgrade\r\nUpgrade: websocket\r\n'))
        fixed=req('POST','/body',b'Content-Length: 5\r\n',b'a\x00b\xffc')
        chunked=req('POST','/body',b'Transfer-Encoding: chunked\r\n',
            b'2;key="a\\\"b"\r\na\x00\r\n3;flag\r\nb\xffc\r\n0\r\nX-Final: yes\r\n\r\n')
        for wire in [req('GET','/echo',b'X-Value: hello\r\n'),fixed,chunked]:
            expected=b'GET /echo hello' if b'/echo' in wire else b'a\x00b\xffc'
            with connect(PORT) as s,s.makefile('rb') as f:
                for split in range(1,len(wire)):
                    s.sendall(wire[:split]); time.sleep(.001); s.sendall(wire[split:]+req())
                    receive(f,expected); receive(f)
                for b in wire:
                    s.sendall(bytes([b])); time.sleep(.001)
                receive(f,expected)
        rng=random.Random(72919)
        for size in [0,1,8191,8192,8193,65536,1048576]:
            body=rng.randbytes(size)
            exchange(req('POST','/body',f'Content-Length: {size}\r\n'.encode(),body),body)
            pieces=[body[i:i+997] for i in range(0,size,997)]
            encoded=b''.join(f'{len(p):X}\r\n'.encode()+p+b'\r\n' for p in pieces)+b'0\r\n\r\n'
            exchange(req('POST','/body',b'Transfer-Encoding: chunked\r\n',encoded),body)
        exchange(req('POST','/trailers',b'Transfer-Encoding: chunked\r\n',b'0\r\nX-Final: yes\r\n\r\n'),b'X-Final=yes')
        with connect(PORT) as s,s.makefile('rb') as f:
            s.sendall(req('HEAD')+req()+req('GET','/status/204')+req()+req('GET','/status/205')+req()+req('GET','/status/304')+req())
            receive(f,head=True); receive(f)
            for status in [204,205,304]: receive(f,b'hidden',status); receive(f)
        headers=exchange(req('GET','/headers'),b'headers')
        assert headers[b'set-cookie']==[b'a=1',b'b=2'] and headers[b'x-test']==[b'yes']
        for framing,body in [(b'Content-Length: 3\r\n',b'abc'),(b'Transfer-Encoding: chunked\r\n',b'3\r\nabc\r\n0\r\n\r\n')]:
            with connect(PORT) as s,s.makefile('rb') as f:
                s.sendall(req('POST','/body',framing+b'Expect: 100-continue\r\n'))
                assert f.readline()==b'HTTP/1.1 100 Continue\r\n'; assert f.readline()==b'\r\n'
                s.sendall(body+req()); receive(f,b'abc'); receive(f)
        with connect(PORT) as delayed,connect(PORT) as other:
            delayed.sendall(req('GET','/deferred',b'X-Value: retained\r\n')+req()); delayed.shutdown(socket.SHUT_WR)
            other.sendall(req())
            with other.makefile('rb') as f: receive(f)
            assert not select.select([delayed],[],[],0)[0], 'deferred handler blocked other client'
            with delayed.makefile('rb') as f:
                receive(f,b'retained'); receive(f); assert f.read(1)==b''
        exchange(req('GET','/resolved'))
        with connect(PORT) as s,s.makefile('rb') as f:
            s.sendall(req(headers=b'Connection: keep-alive, CLOSE\r\n')+req())
            assert receive(f)[b'connection']==[b'close']; assert f.read(1)==b''
        pad=b'GET / HTTP/1.1\r\nHost: localhost\r\nX-Pad: '
        with connect(PORT) as s,s.makefile('rb') as f:
            wire=pad+b'a'*(16384-len(pad)-4)+b'\r\n\r\n'
            s.sendall(wire[:-1]); time.sleep(.005); s.sendall(wire[-1:]+req())
            receive(f); receive(f)
        invalid=[
            (b'GET / HTTP/1.1\r\n\r\n',400),
            (req(headers=b'Host: duplicate\r\n'),400),
            (req(headers=b'Content-Length: 0\r\nContent-Length: 0\r\n'),400),
            (req(headers=b'Transfer-Encoding: chunked\r\nContent-Length: 0\r\n'),400),
            (req(headers=b'Transfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n'),400),
            (req(headers=b'Transfer-Encoding: gzip, chunked\r\n'),501),
            (req(headers=b'Content-Length: +1\r\n'),400),
            (req(headers=b'Content-Length: 0,0\r\n'),400),
            (req(headers=b'Content-Length: 1048577\r\n'),413),
            (req(headers=b'Content-Length: '+b'9'*5000+b'\r\n'),413),
            (req(headers=b'Expect: something\r\n'),417),
            (req('CONNECT','example.com:443'),501),
            (req(target='/bad%'),400),(req(target='/bad%zz'),400),(req(target='/#fragment'),400),
            (req(headers=b'Bad Header: x\r\n'),400),(req(headers=b'X: a\x00b\r\n'),400),
            (req(headers=b' folded: value\r\n'),400),(req(headers=b'X: a\nb\r\n'),400),
            (req(headers=b'X: '+b'x'*17000+b'\r\n'),431),
            (req(target='/fail'),500),(req(target='/deferred-error'),500),
        ]
        for chunk,status in [(b'+1\r\na\r\n0\r\n\r\n',400),(b'1\na\r\n0\r\n\r\n',400),
            (b'1\r\naXX0\r\n\r\n',400),(b'100001\r\n',413),
            (b'1;=x\r\na\r\n0\r\n\r\n',400),(b'1;key="unclosed\r\na\r\n0\r\n\r\n',400),
            (b'0\r\nContent-Length: 1\r\n\r\n',400),(b'0\r\nHost: evil\r\n\r\n',400)]:
            invalid.append((req('POST','/body',b'Transfer-Encoding: chunked\r\n',chunk),status))
        invalid.append((pad+b'a'*(16385-len(pad)-4)+b'\r\n\r\n',431))
        invalid.append((req('POST','/body',b'Transfer-Encoding: chunked\r\n',
            b'0\r\n'+b'X-Final: '+b'a'*900+b'\r\n'+(b'X: a\r\n'*2600)+b'\r\n'),431))
        for wire,status in invalid: reject(wire,status)
        for partial in [b'GET / HTTP/1.1\r\nHost:',req('POST','/body',b'Content-Length: 3\r\n',b'ab'),
            req('POST','/body',b'Transfer-Encoding: chunked\r\n',b'1\r\na\r\n0\r\n')]:
            with connect(PORT) as s:
                s.sendall(partial); s.shutdown(socket.SHUT_WR); assert s.recv(1)==b''
        def worker(i):
            with connect(PORT) as s,s.makefile('rb') as f:
                body=f'client-{i}'.encode(); wire=req('POST','/body',f'Content-Length: {len(body)}\r\n'.encode(),body)
                s.sendall(wire*40)
                for _ in range(40): receive(f,body)
        with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool: list(pool.map(worker,range(32)))
        with connect(PORT) as s,s.makefile('rb') as f:
            s.sendall(req()*8192); time.sleep(.1)
            for _ in range(8192): receive(f)
        for _ in range(150):
            with connect(PORT) as s: s.sendall(req()*4)
        exchange(req())
        results['protocol']={'result':'PASS','all_splits':True,'one_byte_fragments':True,
            'fixed_and_chunked_body_sizes':[0,1,8191,8192,8193,65536,1048576],
            'streaming':'8 MiB, delayed reader, HEAD suppression, producer error, exactly-once release',
            'invalid_cases':len(invalid),'concurrent_pipelined_posts':1280,
            'head_no_body_statuses_trailers_expect_headers_deferred_half_close':'PASS'}
    print(json.dumps(results,indent=2))

if __name__=='__main__': main()
