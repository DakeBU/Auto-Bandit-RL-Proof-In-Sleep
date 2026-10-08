from common_proving_v1 import *

def canary_contract_fixed():
    s=proving_fixed()
    assert load(RUN/'D4-attempt-v2.json')['actual_build_exit']==0
    r=load(RUN/'canary-contract-receipt-v1.json')
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert r['inputs_unchanged'] and not r['required_blocking_repairs']
    assert r['report_sha256']==sha(RUN/'canary-contract-review-v1.md')
    inputs=load(RUN/'canary-contract-review-inputs-v1.json')['rows']
    checks={x['path']:x for x in r['raw_input_checks']}
    assert len(inputs)==r['fixed_input_count'] and set(checks)=={x['path'] for x in inputs}
    for row in inputs:
        c=checks[row['path']]
        assert c['unchanged'] and c['before_sha256']==c['after_sha256']==row['sha256']==sha(row['path'])
    if CANARY.exists():
        text=CANARY.read_text(encoding='utf8')
        prefix=(CONTRACT/'canary-context-v1.lean.txt').read_text(encoding='utf8').rsplit('end Tests.OnlineFTLOscillation',1)[0]
        assert text.startswith(prefix)
        for t in load(CONTRACT/'canary-targets-v1.json')['targets']:
            assert statement_hash(lean_declaration_header(CANARY,t['name']))==t['statement_hash']
    return s
