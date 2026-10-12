from pathlib import Path
import json,hashlib
P=Path('tmp/online-b4-next-attainment-canary-body-20261012').resolve()
def bind(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
rp=P/'focused-v3/receipt.json'
r=json.loads(rp.read_text())
assert r['actual_exit']==0 and r['integrity_pass'] is True
probe=bind(P/'ImportedAudit-construction-v1.lean')
assert probe['sha256']=='590d4454c6280f8c8a6f11747d9f053fcd16f9353217409ec43b28b3b259472a'
m=dict(candidate=bind(P/'scratch-candidate-v3.lean'),olean=bind(P/'StrongConvexAttainmentCanaries.olean'),receipt=bind(rp),probe=probe,output_family=r['output_family'],inputs=[probe])
p=P/'import-input-manifest-v1.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(m,f,indent=2);f.write('\n')
print(json.dumps(bind(p)))
