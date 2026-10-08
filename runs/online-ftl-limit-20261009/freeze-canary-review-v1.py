from common_proving_v1 import *
proving_fixed()
r=load(RUN/'canary-blind-receipt-v1.json')
assert r['inputs_unchanged'] and r['report_sha256']==sha(RUN/'canary-blind-reconstruction-v1.md')
for row in load(RUN/'canary-blind-inputs-v1.json')['rows']:
    assert sha(row['path'])==row['sha256']
paths=[CONTRACT/p for p in ['canary-context-v1.lean.txt','canary-targets-v1.lean.txt','canary-targets-v1.json',
    'canary-plan-v1.md','targets-v1.lean.txt','targets-v1.json','context-v1.lean.txt','source-intent-v1.md','reader-requirements-v1.json']]
paths += [RUN/p for p in ['canary-blind-packet-v1.md','neutral-canary-statements-v1.lean.txt','canary-blind-reconstruction-v1.md',
    'canary-blind-receipt-v1.json','canary-blind-inputs-v1.json','canary-draft-typecheck-v1.lean',
    'canary-draft-typecheck-v1.log','canary-draft-typecheck-v1-exit.json','canary-source-review-packet-v1.md',
    'stabilized-contract-v1.json','source-contract-review-v1.md','source-contract-receipt-v1.json']]
paths += [RUN/('source-pdf%d-text-v1.txt'%p) for p in [14,16,18]]
write(RUN/'canary-contract-review-inputs-v1.json',dict(rows=rows(paths)))
print('Bound exact separate canary-contract inputs:',len(set(paths)),flush=True)
