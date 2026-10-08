from common_v1 import *
fixed()
r=load(RUN/'blind-receipt-v1.json')
assert r['inputs_unchanged'] and r['report_sha256']==sha(RUN/'blind-reconstruction-v1.md')
assert load(RUN/'api-signature-probe-v1-exit.json')['actual_exit']==0
indexed={}
def add(p):
    p=Path(p).resolve();assert p.is_file()
    indexed[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for row in load(RUN/'baseline-v2.json')['rows']:add(ROOT/row['path'])
for d in ['tasks','proof-obligations','conversion-windows']:add(ROOT/d/(TASK+'.md'))
add(PDF)
write(RUN/'source-contract-review-inputs-v1.json',dict(rows=sorted(indexed.values(),key=lambda x:x['path']),
    fixed_input_count=len(indexed),required_reader_corrections=load(CONTRACT/'reader-requirements-v1.json'),
    permitted_future_proof_scope=load(RUN/'contract-mutable-scope-v1.json'),source_correction_requires_separate_verdict=True,
    first_ready_leaf='D1',chapter_complete=False,goal_complete=False))
print('Source contract RAW input count:',len(indexed),'four draft terminals, no theorem body.',flush=True)
