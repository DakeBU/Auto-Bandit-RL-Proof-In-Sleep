from common_v1 import *
from collections import Counter

REVIEW_REPORT_SHA = '8dc077c54eec3214346298baec334194af57e7d5fc88f128618c1abee2b73bd2'
REVIEW_RECEIPT_SHA = '28b51bfa0f8aee4eb4c7cfbda55718240ec8384875d20a3cb0896da1aa4304ac'
APPEND_METADATA = [Path(d)/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','proof-blueprints']]


def reviewed_fixed():
    fixed()
    assert sha(RUN/'source-contract-review-v2.md') == REVIEW_REPORT_SHA
    assert sha(RUN/'source-contract-receipt-v2.json') == REVIEW_RECEIPT_SHA
    receipt=load(RUN/'source-contract-receipt-v2.json')
    assert receipt['verdict']=='accepted-with-explicit-delta'
    assert receipt['before_after_raw_hashes_match'] and not receipt['required_blocking_repairs']
    assert receipt['reader_requirements']==load(CONTRACT/'reader-requirements-v2.json')
    for row in load(RUN/'source-review-inputs-v2.json')['rows']:
        p=Path(row['path'])
        if sha(p)==row['sha256']:
            continue
        snapshot=RUN/'snapshots'/('CONTRACT-reviewed--'+p.as_posix().replace('/','--')+'.raw')
        assert snapshot.exists() and sha(snapshot)==row['sha256'], p
        if p in APPEND_METADATA or p.as_posix() in ['BanditRLProof.lean','Tests.lean']:
            assert p.read_bytes().startswith(snapshot.read_bytes()), p
        elif p.as_posix()=='research-wiki/retrieval-index/local_lean_declarations.json':
            old=load(snapshot)['declarations']; now=load(p)['declarations']
            canonical=lambda r:json.dumps(r,sort_keys=True,ensure_ascii=False)
            a=Counter(map(canonical,old));b=Counter(map(canonical,now))
            assert all(b[k]>=v for k,v in a.items()), p
        else:
            raise AssertionError('Frozen CONTRACT input changed: '+p.as_posix())
    return receipt


def headers_fixed(count):
    reviewed_fixed()
    text=PUBLIC.read_text(encoding='utf8')
    context=(CONTRACT/'public-context-v2.lean').read_text(encoding='utf8')
    context=context[:context.index('end BanditRL.OnlineLearning')]
    assert text.startswith(context)
    for row in load(CONTRACT/'targets-v2.json')['rows'][:count]:
        assert text.count(row['header']+' := by')==1, row['id']
