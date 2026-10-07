from common_accepted_v1 import *
accepted_fixed()
assert load(RUN/'committed-raw-audit-v2.json')['status']=='passed-at-explicit-audited-head'
assert load(RUN/'full-harness-final-v1-exit.json')['exit_code']==0
paths=[PUBLIC,CANARY,RUN/'final-reader-review-v1.md',RUN/'final-reader-receipt-v1.json',RUN/'accepted-decision-v1.json',RUN/'publication-order-repair-v2.json',RUN/'committed-raw-audit-v1.log',RUN/'committed-raw-audit-v1-exit.json',RUN/'committed-raw-audit-v2.json',RUN/'full-harness-final-v1.log',RUN/'full-harness-final-v1-exit.json',RUN/'PR-body-v1.md',RUN/'pr-payload-v1.json']
write(RUN/'publication-repair-review-inputs-v3.json',dict(scope='Publication metadata repair only; exact previously accepted mathematics, reader content and original receipts unchanged. Reconcile the preserved raw audit failure and actual direct-success plus final harness. Concrete draft PR payload is authorized, not yet executed.',rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in paths],requested_model='GPT-6 Astra',requested_reasoning_effort='medium',runtime_attested=False,chapter_complete=False,goal_complete=False))
print('Frozen',len(paths),'publication repair bindings; no proof/header/reader changes')
