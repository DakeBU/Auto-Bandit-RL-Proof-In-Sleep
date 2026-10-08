from common_canary_v1 import *

ROUTE = 'online-foundations'
READERS = [ROOT/'website/content'/(n+'.json') for n in ['readings','highlights','chapters']]
CONTRIBUTION = ROOT/'research-wiki/contribution-contracts/online-kernel-causal-20261008.json'

def baseline(rel):
    row = next(x for x in load(RUN/'draft-baseline-v1.json')['rows'] if x['path'] == str(rel))
    assert sha(ROOT/row['snapshot']) == row['sha256']
    return (ROOT/row['snapshot']).read_bytes()

def body_fixed(integrated=False):
    authority = load(RUN/'body-review-authority-v1.json')
    assert sha(RUN/'public-body-receipt-v1.json') == authority['receipt_sha256']
    assert sha(RUN/'public-body-review-v1.md') == authority['report_sha256']
    r = load(RUN/'public-body-receipt-v1.json')
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and r['inputs_unchanged']
    assert r['fixed_input_count'] == 350 and not r['required_blocking_repairs']
    assert r['approved_future_exact_scope'] == load(RUN/'body-future-integration-scope-v1.json')
    assert r['required_reader_corrections'] == load(CONTRACT/'reader-requirements-v1.json')
    binding = load(RUN/'body-bindings-v1.json')
    assert sha(PUBLIC) == binding['public_sha256'] and sha(CANARY) == binding['canary_sha256']
    assert sha(RUN/'reader-proposal-v1.json') == binding['reader_proposal_sha256']
    assert sha(RUN/'body-future-integration-scope-v1.json') == binding['future_scope_sha256']
    s = load(RUN/'stabilized-contract-v1.json')
    for p,h in [(CONTRACT/'targets-v2.json',s['targets_sha256']),
                (CONTRACT/'targets-v1.lean.txt',s['headers_sha256']),
                (CONTRACT/'context-v2.lean.txt',s['context_sha256']),
                (CONTRACT/'source-intent-v1.md',s['source_intent_sha256']),
                (RUN/'source-contract-receipt-v1.json',s['receipt_sha256']),
                (RUN/'source-contract-review-v1.md',s['report_sha256'])]:
        assert sha(p) == h
    context = (CONTRACT/'context-v2.lean.txt').read_text(encoding='utf8').rsplit('end BanditRL.OnlineLearning',1)[0]
    assert PUBLIC.read_text(encoding='utf8').startswith(context)
    for t in s['targets']:
        assert statement_hash(lean_declaration_header(PUBLIC,t['name'])) == t['statement_hash']
    for t in load(RUN/'canary-frozen-targets-v2.json')['targets']:
        assert statement_hash(lean_declaration_header(CANARY,t['name'])) == t['statement_hash']
    roots = [ROOT/'BanditRLProof.lean',ROOT/'Tests.lean']+READERS
    snapshots = {x['path']:x for x in authority['mutable_snapshots']}
    baseline_fixed(mutable=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl']+
        ([p.relative_to(ROOT).as_posix() for p in roots] if integrated else []))
    for row in load(RUN/'body-review-inputs-v1.json')['rows']:
        p = Path(row['path'])
        if sha(p) == row['sha256']:
            continue
        if p.resolve() == (RUN/'common_canary_v1.py').resolve():
            repair = load(RUN/'helper-eof-repair-authority-v1.json')
            assert sha(RUN/'helper-eof-receipt-v1.json') == repair['receipt_sha256']
            assert sha(RUN/'helper-eof-review-v1.md') == repair['report_sha256']
            rr = load(RUN/'helper-eof-receipt-v1.json')
            assert rr['verdict'] == 'accepted' and rr['inputs_unchanged'] and rr['fixed_input_count'] == 22
            assert not rr['required_blocking_repairs']
            assert rr['report_sha256'] == repair['report_sha256']
            assert sha(repair['original_snapshot']) == row['sha256'] == repair['old_sha256']
            assert sha(repair['new_snapshot']) == repair['new_sha256'] == sha(p)
            assert Path(repair['original_snapshot']).read_bytes() == p.read_bytes()+b'\n'
            continue
        if p.as_posix() in snapshots:
            old = Path(snapshots[p.as_posix()]['snapshot']).read_bytes()
            assert hashlib.sha256(old).hexdigest() == row['sha256']
            now = p.read_bytes()
            assert now.startswith(old), p
            if p.suffix == '.jsonl':
                suffix = [json.loads(line) for line in now[len(old):].decode('utf8').splitlines() if line.strip()]
                assert all(x.get('task',x.get('session_id')) == TASK for x in suffix), p
            continue
        assert integrated and p.resolve() in {x.resolve() for x in roots}, p
        assert hashlib.sha256(baseline(p.relative_to(ROOT).as_posix())).hexdigest() == row['sha256']
    return r

def fixed_integrated():
    r = body_fixed(True)
    proposal = load(RUN/'reader-proposal-v1.json')
    for rel,addition in r['approved_future_exact_scope']['exact_root_additions'].items():
        assert (ROOT/rel).read_bytes() == baseline(rel)+addition.encode('utf8')
    for label in ['readings','highlights','chapters']:
        old = json.loads(baseline('website/content/'+label+'.json').decode('utf8'))
        new = load(ROOT/'website/content'/(label+'.json'))
        assert set(old) == set(new)
        assert {k:v for k,v in old.items() if k!=label} == {k:v for k,v in new.items() if k!=label}
        if label == 'highlights':
            assert new[label] == old[label]+proposal['notes']
        else:
            assert len(new[label]) == len(old[label])
            for a,b in zip(old[label],new[label]):
                if a['slug'] != ROUTE:
                    assert a == b
                elif label == 'readings':
                    assert {k:v for k,v in a.items() if k!='source_theorems'} == {k:v for k,v in b.items() if k!='source_theorems'}
                    assert b['source_theorems'] == a['source_theorems']+[proposal['card']]
                else:
                    assert {k:v for k,v in a.items() if k not in ['module_globs','completion_blockers','open_gaps']} == \
                        {k:v for k,v in b.items() if k not in ['module_globs','completion_blockers','open_gaps']}
                    assert b['module_globs'] == a['module_globs']+[PUBLIC.relative_to(ROOT).as_posix()]
                    for k in ['completion_blockers','open_gaps']:
                        assert b[k] == a[k]+[proposal['boundary']]
    manifest = load(CONTRIBUTION)
    assert manifest['id'] == TASK
    assert manifest['declarations'] == [t['name'] for t in load(RUN/'stabilized-contract-v1.json')['targets']]
    assert manifest['affected_files'] == [PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+\
        [p.relative_to(ROOT).as_posix() for p in READERS]
    return True
