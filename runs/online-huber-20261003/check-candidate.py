from pathlib import Path
import json,hashlib,subprocess,sys
root=Path(__file__).resolve().parents[2]
run=Path(__file__).resolve().parent
c=root/'docs/contracts/online-huber-derivative-v1'
p=run/'candidate.lean.txt'
s=p.read_text(encoding='utf-8-sig')
ctx=json.loads((c/'context.json').read_text(encoding='utf-8'))
assert s.startswith(ctx['prefix'])
assert hashlib.sha256(ctx['prefix'].encode()).hexdigest()==ctx['sha256']
reports=[]
for n in json.loads((c/'headers.json').read_text(encoding='utf-8')):
 q=subprocess.run([sys.executable,str(root/'tools/bandit.py'),'safe-verify','--fence',str(c/(n+'.json')),'--lean-file',str(p)],capture_output=True,cwd=root,check=True)
 reports.append(json.loads(q.stdout))
print(json.dumps({'headers':reports,'context_passed':True,'source_lf_sha256':hashlib.sha256(s.encode()).hexdigest()},indent=2))
