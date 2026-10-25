#!/usr/bin/env python3
"""Event delivery, notification floods, reset/FIN and post-shutdown sends."""
import argparse, concurrent.futures, hashlib, json, os, pathlib, secrets, socket, struct, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--binary',type=pathlib.Path,default=ROOT/'.lake/build/bin/uv_wakeup_test');p.add_argument('--output',type=pathlib.Path,default=ROOT/'results/wakeup.json');a=p.parse_args()
seed=secrets.randbits(64);rows=[]
for rep in range(6):
 with socket.socket() as reserve:
  reserve.bind(('127.0.0.1',0));port=reserve.getsockname()[1]
 proc=subprocess.Popen([str(a.binary),str(port)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,env={**os.environ,'LEAN_NUM_THREADS':'1'})
 try:
  for _ in range(200):
   try:
    with socket.create_connection(('127.0.0.1',port),.02):break
   except OSError:
    assert proc.poll() is None,proc.communicate();time.sleep(.005)
  def client(i):
   with socket.create_connection(('127.0.0.1',port),2) as s:
    s.settimeout(4);s.sendall(b'reset' if i%3==0 else str(seed+i).encode())
    if i%3==0:
     s.setsockopt(socket.SOL_SOCKET,socket.SO_LINGER,struct.pack('ii',1,0));return 0
    if i%3==1:s.shutdown(socket.SHUT_WR)
    data=b''
    while True:
     chunk=s.recv(65536)
     if not chunk:break
     data+=chunk
    assert data and data.replace(b'wake\n',b'')==b'',(i,data[:100])
    return len(data)//5
  with concurrent.futures.ThreadPoolExecutor(max_workers=24) as pool:counts=list(pool.map(client,range(24)))
  stdout,stderr=proc.communicate(timeout=10)
  assert proc.returncode==0 and 'PASS notifications=' in stdout,(stdout,stderr)
  rows.append({'repetition':rep,'received_callbacks':sum(counts),'stdout':stdout,'stderr':stderr})
 finally:
  if proc.poll() is None:proc.kill();proc.wait()
a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(json.dumps({'passed':True,'seed':seed,'connections':144,'binary_sha256':hashlib.sha256(a.binary.read_bytes()).hexdigest(),'runs':rows},indent=2)+'\n')
print('PASS: 144 connections; flood, half-close, reset and late post-shutdown notifications')
