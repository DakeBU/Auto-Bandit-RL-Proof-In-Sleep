import hashlib,json,re
from pathlib import Path
r=Path('E:/ABRL/worktrees/research-online-book')
d=r/'tmp/online-support-owner-repaired-gates-20261012/combined-axiom-audit-v1'
receipt=json.loads((d/'receipt.json').read_bytes())
assert receipt['actual_exit']==0 and receipt['capture_integrity_ok']
assert receipt['pre_git']['HEAD']==receipt['post_git']['HEAD']=='95cfc51fa11619217f8153614d5b5b8a6c04aa2d'
raw=(d/'stdout.raw').read_bytes()
rows=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",raw.decode('utf-8'),re.S)
assert len(rows)==10 and len({n for n,a in rows})==10
decl={n:[x.strip() for x in a.split(',')] for n,a in rows}
assert all(set(a)=={'propext','Classical.choice','Quot.sound'} for a in decl.values())
out=dict(kind='parsed actual audit stdout',source_head=receipt['pre_git']['HEAD'],receipt_sha256=hashlib.sha256((d/'receipt.json').read_bytes()).hexdigest(),stdout_sha256=hashlib.sha256(raw).hexdigest(),declarations=decl,standard_axioms_only=True)
with (Path(__file__).parent/'owner-repaired-combined-axiom-parsed-v1.json').open('x',encoding='utf-8') as f:json.dump(out,f,indent=2)
print(json.dumps({'declarations':len(decl),'standard_axioms_only':True}))
