from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
def bind(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
r=P/'focused-v1/receipt.json';receipt=json.loads(r.read_text(encoding='utf-8'))
assert receipt['actual_exit']==0 and receipt['integrity_pass']
op=P/'CumulativeOptimisticStabilityDualCandidate.olean'
assert bind(op)==receipt['output_olean']
mi=dict(probe=bind(P/'ImportedAudit-v1.lean'),candidate=bind(P/'candidate-v1.lean'),olean=bind(op),receipt=bind(r),inputs=[bind(P/n) for n in ['ImportedAudit-v1.lean','scratch-frozen-header-v1.txt','HeaderElaboration-v2.lean','closure-manifest-v1.json','header-origins-v1.json']])
out=P/'import-manifest-v1.json'
with out.open('x',encoding='utf-8') as f:json.dump(mi,f,indent=2)
print(json.dumps(dict(import_manifest=bind(out),body_receipt=bind(r))))
