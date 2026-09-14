"""Verify the frozen extended-real convexity headers and definition context; not a Lean build."""
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
contracts=root/'docs/contracts/online-optimality-v1'
module=root/'BanditRLProof/OnlineConvexOptimality.lean'
headers=json.loads((contracts/'headers.json').read_text(encoding='utf-8'))
reports=[]
for name in headers:
 p=subprocess.run([sys.executable,str(root/'tools/bandit.py'),'safe-verify','--fence',str(contracts/(name+'.json')),'--lean-file',str(module)],cwd=root,capture_output=True)
 if p.returncode:
  sys.stderr.buffer.write(p.stdout+p.stderr);raise SystemExit(p.returncode)
 reports.append(json.loads(p.stdout))
ctx=json.loads((contracts/'context.json').read_text(encoding='utf-8'));source=module.read_text(encoding='utf-8-sig')
assert source.startswith(ctx['prefix'])
assert hashlib.sha256(ctx['prefix'].encode()).hexdigest()==ctx['sha256']
print(json.dumps({'headers':reports,'context_passed':True,'source_lf_sha256':hashlib.sha256(source.encode()).hexdigest()},indent=2))
