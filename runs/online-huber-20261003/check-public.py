from pathlib import Path
import json,hashlib,subprocess,sys
root=Path(__file__).resolve().parents[2];c=root/'docs/contracts/online-huber-public-v1'
m=json.loads((c/'integration.json').read_text(encoding='utf-8'));p=root/m['source_file']
digest=hashlib.sha256(p.read_text(encoding='utf-8-sig').encode()).hexdigest()
assert digest==m['source_lf_sha256'], 'Public integration source changed; review required'
reports=[]
for n in json.loads((c/'headers.json').read_text(encoding='utf-8')):
 q=subprocess.run([sys.executable,str(root/'tools/bandit.py'),'safe-verify','--fence',str(c/(n+'.json')),'--lean-file',str(p)],capture_output=True,cwd=root,check=True)
 reports.append(json.loads(q.stdout))
print(json.dumps({'headers':reports,'source_context_and_bodies_unchanged':True,'source_lf_sha256':digest},indent=2))
