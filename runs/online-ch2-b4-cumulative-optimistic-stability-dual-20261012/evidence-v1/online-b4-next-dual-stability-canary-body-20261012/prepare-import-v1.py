from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
def bind(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
r=P/'focused-v2/receipt.json';q=json.loads(r.read_text(encoding='utf-8'))
assert q['actual_exit']==0 and q['integrity_pass']
op=P/'CumulativeOptimisticStabilityDualCanary.olean';assert bind(op)==q['output_olean']
mi=dict(probe=bind(P/'ImportedAudit-v2.lean'),candidate=bind(P/'candidate-v2.lean'),olean=bind(op),receipt=bind(r),inputs=[bind(P/n) for n in ['ImportedAudit-v2.lean','HeaderElaboration-v1.lean','closure-manifest-v1.json']])
out=P/'import-manifest-v1.json'
with out.open('x',encoding='utf-8') as f:json.dump(mi,f,indent=2)
print(json.dumps(dict(manifest=bind(out),body_receipt=bind(r),candidate=mi['candidate'])))
