from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash

def proving_fixed():
    baseline_fixed(mutable=['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl'])
    s=load(RUN/'stabilized-contract-v1.json')
    assert sha(RUN/'source-contract-receipt-v1.json')==s['receipt_sha256']
    assert sha(RUN/'source-contract-review-v1.md')==s['report_sha256']
    assert sha(CONTRACT/'targets-v1.json')==s['targets_sha256']
    assert sha(CONTRACT/'targets-v1.lean.txt')==s['headers_sha256']
    assert sha(CONTRACT/'source-intent-v1.md')==s['source_intent_sha256']
    mutable={r['path']:r for r in s['mutable_reviewed_snapshots']}
    for row in load(RUN/'source-contract-review-inputs-v1.json')['rows']:
        if sha(row['path'])==row['sha256']:continue
        assert row['path'] in mutable,row['path']
        bound=mutable[row['path']]
        assert sha(bound['snapshot'])==row['sha256']
        assert Path(row['path']).read_bytes().startswith(Path(bound['snapshot']).read_bytes())
    if PUBLIC.exists():
        text=PUBLIC.read_text(encoding='utf8')
        for t in s['targets']:
            if 'theorem '+t['name'].split('.')[-1] not in text:continue
            assert statement_hash(lean_declaration_header(PUBLIC,t['name']))==t['statement_hash'],t['id']
    return s
