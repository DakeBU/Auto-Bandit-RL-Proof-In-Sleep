from common_v1 import *
REVIEW_SHA = '53edeb2876e1972bd5d9ad0e4fadf913f22f18285a84be8c88399d80dd067753'
REPORT_SHA = 'd904bb387ee2d5b3a225bde7b1e54bafa49c0a10090e8c673ddbec7ca0288251'
APPEND_METADATA = [Path(d)/(TASK+'.md') for d in
    ['tasks','proof-obligations','proof-blueprints','conversion-windows']]

def reviewed_fixed():
    fixed()
    assert sha(RUN/'source-contract-receipt-v1.json')==REVIEW_SHA
    assert sha(RUN/'source-contract-review-v1.md')==REPORT_SHA
    r=load(RUN/'source-contract-receipt-v1.json')
    assert r['verdict']=='accepted-with-explicit-delta' and r['inputs_unchanged']
    assert not r['required_blocking_repairs'] and not r['body_accepted']
    for p,h in load(RUN/'source-review-inputs-v1.json')['fixed_inputs'].items():
        assert sha(p)==h,p
    return r

def headers_fixed(count):
    reviewed_fixed()
    text=PUBLIC.read_text(encoding='utf8')
    rows=load(CONTRACT/'targets-v1.json')['targets']
    assert text.count('\ntheorem ')==count
    for row in rows[:count]:
        assert row['header']+' := by\n' in text,row['name']
    assert not any(s in text for s in ['sorry','admit','axiom','postulate'])
