import json,hashlib,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
c=root/'docs/contracts/online-minorant-v1';m=root/'BanditRLProof/OnlineConvexMinorant.lean'
s=m.read_text(encoding='utf-8');hs=json.loads((c/'headers.json').read_text(encoding='utf-8'));reports=[]
for n in hs:
 p=subprocess.run([sys.executable,str(root/'tools/bandit.py'),'safe-verify','--fence',str(c/(n+'.json')),'--lean-file',str(m)],capture_output=True,cwd=root)
 if p.returncode:sys.stderr.buffer.write(p.stdout+p.stderr);raise SystemExit(p.returncode)
 reports.append(json.loads(p.stdout))
ctx=json.loads((c/'context.json').read_text(encoding='utf-8'))
for a in ctx['chunks']:
 assert a['text'] in s and hashlib.sha256(a['text'].encode()).hexdigest()==a['sha256']
assert s.startswith(ctx['chunks'][0]['text'])
print(json.dumps({'headers':reports,'context_passed':True,'source_lf_sha256':hashlib.sha256(s.encode()).hexdigest()},indent=2))
