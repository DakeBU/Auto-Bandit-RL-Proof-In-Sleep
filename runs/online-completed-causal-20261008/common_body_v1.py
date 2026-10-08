from common_proving_v1 import *

BODY_SHA='0f527164b43e2536c50468ec80ace741ba7c7a43af7507584a1670a046354b06'
BODY_REPORT_SHA='3d3d6010701b2a7a1141fd59f533bfe0517f2e89d0ff7b6896075644b016fdf9'
ROUTE='online-foundations'
READERS=[ROOT/'website/content'/(n+'.json') for n in ['readings','highlights','chapters']]
MANIFEST=ROOT/'research-wiki/contribution-contracts/online-completed-causal-20261008.json'
def baseline(rel):
    row=next(x for x in load(RUN/'draft-baseline-v1.json')['rows'] if x['path']==str(rel))
    assert sha(ROOT/row['snapshot'])==row['sha256']
    return (ROOT/row['snapshot']).read_bytes()
def body_fixed(integrated=False):
    allowed=[ROOT/'BanditRLProof.lean',ROOT/'Tests.lean']+READERS
    baseline_fixed(mutable=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl']+
        ([p.relative_to(ROOT).as_posix() for p in allowed] if integrated else []))
    assert sha(RUN/'public-body-receipt-v1.json')==BODY_SHA
    assert sha(RUN/'public-body-review-v1.md')==BODY_REPORT_SHA
    r=load(RUN/'public-body-receipt-v1.json')
    assert r['verdict']=='accepted-with-explicit-delta' and r['inputs_unchanged']
    assert r['fixed_input_count']==285 and not r['required_blocking_repairs']
    assert r['approved_future_exact_scope']==load(RUN/'body-future-integration-scope-v1.json')
    assert r['required_reader_corrections']==load(CONTRACT/'reader-requirements-v1.json')
    b=load(RUN/'body-bindings-v1.json')
    assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
    s=load(RUN/'stabilized-contract-v1.json')
    for p,h in [(CONTRACT/'targets-v1.json',s['targets_sha256']),
        (CONTRACT/'targets-v1.lean.txt',s['headers_sha256']),
        (CONTRACT/'source-intent-v1.md',s['source_intent_sha256']),
        (RUN/'source-contract-receipt-v1.json',s['receipt_sha256']),
        (RUN/'source-contract-review-v1.md',s['report_sha256'])]:assert sha(p)==h
    for t in s['targets']:assert statement_hash(lean_declaration_header(PUBLIC,t['name']))==t['statement_hash']
    for row in load(RUN/'body-review-inputs-v1.json')['rows']:
        p=Path(row['path'])
        if sha(p)==row['sha256']:continue
        assert integrated and p.resolve() in {x.resolve() for x in allowed},p
        assert hashlib.sha256(baseline(p.relative_to(ROOT).as_posix())).hexdigest()==row['sha256']
    return r
def fixed_integrated():
    r=body_fixed(True);proposal=load(RUN/'reader-proposal-v1.json')
    for rel,addition in r['approved_future_exact_scope']['exact_root_additions'].items():
        assert (ROOT/rel).read_bytes()==baseline(rel)+addition.encode()
    for label in ['readings','highlights','chapters']:
        old=json.loads(baseline('website/content/'+label+'.json').decode('utf8'))
        new=load(ROOT/'website/content'/(label+'.json'))
        assert set(old)==set(new)
        assert {k:v for k,v in old.items() if k!=label}=={k:v for k,v in new.items() if k!=label}
        if label=='highlights':assert new[label]==old[label]+proposal['notes']
        else:
            assert len(new[label])==len(old[label])
            for a,b in zip(old[label],new[label]):
                if a['slug']!=ROUTE:assert a==b
                elif label=='readings':
                    assert {k:v for k,v in a.items() if k!='source_theorems'}=={k:v for k,v in b.items() if k!='source_theorems'}
                    assert b['source_theorems']==a['source_theorems']+[proposal['card']]
                else:
                    assert {k:v for k,v in a.items() if k not in ['module_globs','completion_blockers','open_gaps']}=={k:v for k,v in b.items() if k not in ['module_globs','completion_blockers','open_gaps']}
                    assert b['module_globs']==a['module_globs']+[PUBLIC.relative_to(ROOT).as_posix()]
                    for k in ['completion_blockers','open_gaps']:assert b[k]==a[k]+[proposal['boundary']]
    assert load(MANIFEST)['id']==TASK
    assert load(MANIFEST)['declarations']==[t['name'] for t in load(CONTRACT/'targets-v1.json')['targets']]
    assert load(MANIFEST)['affected_files']==[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS]
    return True
