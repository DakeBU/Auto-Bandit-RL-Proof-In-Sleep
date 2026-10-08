from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

def proving_fixed():
    fixed()
    s=load(RUN/'stabilized-contract-v1.json')
    for p,h in [(RUN/'source-contract-receipt-v1.json',s['receipt_sha256']),
        (RUN/'source-contract-review-v1.md',s['report_sha256']),
        (CONTRACT/'targets-v1.lean.txt',s['headers_sha256']),
        (CONTRACT/'context-v1.lean.txt',s['context_sha256']),
        (CONTRACT/'source-intent-v1.md',s['source_intent_sha256'])]:
        assert sha(p)==h,p
    mutable={r['path']:r for r in s['snapshots']}
    for row in load(RUN/'source-contract-review-inputs-v1.json')['rows']:
        if row['path'] in mutable:
            before=Path(mutable[row['path']]['snapshot']).read_bytes()
            assert hashlib.sha256(before).hexdigest()==row['sha256']
            assert Path(row['path']).read_bytes().startswith(before)
        else:
            assert sha(row['path'])==row['sha256'],row['path']
    if PUBLIC.exists():
        text=PUBLIC.read_text(encoding='utf8')
        prefix=(CONTRACT/'context-v1.lean.txt').read_text(encoding='utf8').rsplit('end BanditRL.OnlineLearning',1)[0]
        assert text.startswith(prefix)
        for t in s['targets']:
            if '\ntheorem '+t['name'].split('.')[-1] in text:
                assert statement_hash(lean_declaration_header(PUBLIC,t['name']))==t['statement_hash'],t['id']
    return s
