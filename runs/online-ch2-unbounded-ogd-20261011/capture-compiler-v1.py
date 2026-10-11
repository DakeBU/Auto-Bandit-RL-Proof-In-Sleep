from pathlib import Path
import subprocess,json,hashlib,datetime,sys,os
ROOT=Path(__file__).resolve().parents[2]
RUN=Path(__file__).resolve().parent
label=sys.argv[1];argv=sys.argv[2:]
assert not (RUN/(label+'.json')).exists()
inputs=[]
for rel in ['BanditRLProof/OnlineUnboundedOGD.lean','BanditRLProof/OnlineUnboundedOSD.lean','BanditRLProof/OnlineGradientDescentSource.lean','BanditRLProof/OnlineGradientDescentVariable.lean']:
 p=ROOT/rel;b=p.read_bytes();snap=RUN/(label+'-'+p.name+'.txt')
 with snap.open('xb') as f:f.write(b)
 inputs.append({'path':rel,'raw_sha256':hashlib.sha256(b).hexdigest(),'snapshot':snap.name})
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
p=subprocess.run(argv,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONIOENCODING='utf-8'))
end=datetime.datetime.now(datetime.timezone.utc).isoformat()
for key,data in [('stdout',p.stdout),('stderr',p.stderr)]:
 with (RUN/(label+'-'+key+'.txt')).open('xb') as f:f.write(data)
row={'argv':argv,'cwd':str(ROOT),'start_utc':start,'end_utc':end,'actual_exit':p.returncode,'inputs':inputs,'inputs_unchanged':all(hashlib.sha256((ROOT/x['path']).read_bytes()).hexdigest()==x['raw_sha256'] for x in inputs),'stdout_sha256':hashlib.sha256(p.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(p.stderr).hexdigest(),'stdout':p.stdout.decode('utf-8','replace'),'stderr':p.stderr.decode('utf-8','replace')}
with (RUN/(label+'.json')).open('xb') as f:f.write((json.dumps(row,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps(row,ensure_ascii=True))
