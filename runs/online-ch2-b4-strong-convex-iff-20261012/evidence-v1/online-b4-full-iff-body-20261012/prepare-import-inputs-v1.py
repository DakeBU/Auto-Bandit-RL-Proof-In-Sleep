from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
def rec(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
obj=dict(probe=rec(P/'ImportedAudit-v1.lean'),candidate_source=rec(P/'candidate-v1.lean'),scratch_olean=rec(P/'FullIffCandidate.olean'),body_receipt=rec(P/'focused-v1/receipt.json'),all_probe_inputs=[rec(P/'ImportedAudit-v1.lean')])
with (P/'import-inputs-v1.json').open('x',encoding='utf-8') as f:json.dump(obj,f,indent=2)
print(json.dumps(rec(P/'import-inputs-v1.json')))
