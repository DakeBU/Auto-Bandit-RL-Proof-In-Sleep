from common_proving_v1 import *
proving_fixed()
assert load(RUN/'D4-attempt-v2.json')['actual_build_exit']==0
r=load(RUN/'canary-blind-receipt-v1.json')
assert r['inputs_unchanged'] and r['report_sha256']==sha(RUN/'canary-blind-reconstruction-v1.md')
for row in load(RUN/'canary-blind-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
paths=list(CONTRACT.glob('*'))+[PUBLIC,PDF]
paths += [RUN/p for p in ['canary-blind-packet-v1.md','neutral-canary-statements-v1.lean.txt',
    'canary-blind-reconstruction-v1.md','canary-blind-receipt-v1.json','canary-blind-inputs-v1.json',
    'canary-draft-typecheck-v1.lean','canary-draft-typecheck-v1.log','canary-draft-typecheck-v1-exit.json',
    'canary-source-review-packet-v1.md','stabilized-contract-v1.json','source-contract-review-v1.md',
    'source-contract-receipt-v1.json','D4-attempt-v1.json','D4-focused-v1.log','D4-focused-v1-exit.json',
    'D4-attempt-v2.json','D4-focused-v2.log','D4-focused-v2-exit.json']]
paths += [RUN/('source-pdf%d%s-v1.%s'%(p,suffix,ext)) for p in [14,16,18] for suffix,ext in [('', 'png'),('-text','txt')]]
write(RUN/'canary-contract-review-inputs-v1.json',dict(rows=rows(paths),fixed_input_count=len(set(paths)),
    public_body_acceptance=False,scope='Separate exact eleven canary headers/context before test proof'))
print('Frozen separate canary review RAW inputs:',len(set(paths)),flush=True)
