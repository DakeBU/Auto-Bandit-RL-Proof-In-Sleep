from pathlib import Path
import subprocess,json,hashlib,datetime,sys,os
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
label=sys.argv[1]; argv=sys.argv[2:]
assert label and not (OUT/(label+'.json')).exists()
inputs=[]
for rel in ['BanditRLProof/OnlinePrescientEuclidean.lean','BanditRLProof/OnlinePrescientBregmanSource.lean','BanditRLProof/OnlinePrescientBregmanRegret.lean','BanditRLProof/OnlinePrescientBregman.lean','BanditRLProof/OnlineBregmanProximal.lean','docs/contracts/online-ch2-prescient-euclidean-v1/neutral-frozen-headers-v1.txt']:
 p=ROOT/rel; b=p.read_bytes();snap=OUT/(label+'-'+p.name+'.snapshot')
 with snap.open('xb') as f:f.write(b)
 inputs.append(dict(path=rel,raw_sha256=hashlib.sha256(b).hexdigest(),snapshot=snap.name))
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
p=subprocess.run(argv,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONIOENCODING='utf-8'))
end=datetime.datetime.now(datetime.timezone.utc).isoformat()
for key,b in [('stdout',p.stdout),('stderr',p.stderr)]:
 with (OUT/(label+'.'+key)).open('xb') as f:f.write(b)
row=dict(argv=argv,cwd=str(ROOT),start_utc=start,end_utc=end,actual_exit=p.returncode,inputs=inputs,inputs_unchanged=all(hashlib.sha256((ROOT/x['path']).read_bytes()).hexdigest()==x['raw_sha256'] for x in inputs),stdout_file=label+'.stdout',stderr_file=label+'.stderr',stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest(),helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),failure_kind='IMPLEMENTATION_FAILED' if p.returncode else None,requested_model='GPT-6 Astra',requested_effort='medium',runtime_attestation=False)
with (OUT/(label+'.json')).open('xb') as f:f.write((json.dumps(row,indent=2)+'\n').encode('utf-8'))
print(json.dumps(row))
