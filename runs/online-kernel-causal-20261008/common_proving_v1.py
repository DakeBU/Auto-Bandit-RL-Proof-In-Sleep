from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

def proving_fixed():
    baseline_fixed(mutable=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl'])
    s = load(RUN / 'stabilized-contract-v1.json')
    for p,h in [(RUN/'source-contract-receipt-v1.json',s['receipt_sha256']),
                (RUN/'source-contract-review-v1.md',s['report_sha256']),
                (CONTRACT/'targets-v2.json',s['targets_sha256']),
                (CONTRACT/'targets-v1.lean.txt',s['headers_sha256']),
                (CONTRACT/'context-v2.lean.txt',s['context_sha256']),
                (CONTRACT/'source-intent-v1.md',s['source_intent_sha256'])]:
        assert sha(p) == h, p
    mutable = {x['path']:x for x in s['mutable_reviewed_snapshots']}
    for row in load(RUN/'source-contract-review-inputs-v1.json')['rows']:
        if sha(row['path']) == row['sha256']:
            continue
        assert row['path'] in mutable, row['path']
        before = Path(mutable[row['path']]['snapshot']).read_bytes()
        assert hashlib.sha256(before).hexdigest() == row['sha256']
        now = Path(row['path']).read_bytes()
        assert now.startswith(before)
        if row['path'].endswith('.jsonl'):
            suffix = [json.loads(line) for line in now[len(before):].decode('utf8').splitlines() if line.strip()]
            assert all(x.get('task',x.get('session_id')) == TASK for x in suffix), row['path']
    if PUBLIC.exists():
        text = PUBLIC.read_text(encoding='utf8')
        context = (CONTRACT/'context-v2.lean.txt').read_text(encoding='utf8').rsplit('end BanditRL.OnlineLearning',1)[0]
        assert text.startswith(context), 'Frozen actual causal definitions changed'
        for target in s['targets']:
            if '\ntheorem '+target['name'].split('.')[-1] not in text:
                continue
            assert statement_hash(lean_declaration_header(PUBLIC,target['name'])) == target['statement_hash']
    return s
