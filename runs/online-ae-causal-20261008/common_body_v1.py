from common_proving_v1 import *

BODY_SHA='9e945f99b219bf7338b645b6486ebada4f33a10e664c54e9018bcc4955efb3cc'
BODY_REPORT_SHA='1f2eec0c3a2d48d2eca3c56aa02fb9348924b2d36d4db7fa2ac204bc8aab3bbf'
CANARY=ROOT/'Tests/OnlineGuessingAECausalCanary.lean'
ROUTE='online-foundations'
READERS=[ROOT/'website/content'/(n+'.json') for n in ['readings','highlights','chapters']]
MANIFEST=ROOT/'research-wiki/contribution-contracts/online-ae-causal-20261008.json'

def baseline(rel):
    row=next(x for x in load(RUN/'draft-baseline-v1.json')['rows'] if x['path']==str(rel))
    assert sha(ROOT/row['snapshot'])==row['sha256']
    return (ROOT/row['snapshot']).read_bytes()

def body_fixed(integrated=False):
    baseline_fixed(mutable=['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl']+
        (['BanditRLProof.lean','Tests.lean']+[p.relative_to(ROOT).as_posix() for p in READERS] if integrated else []))
    assert sha(RUN/'public-body-receipt-v1.json')==BODY_SHA
    assert sha(RUN/'public-body-review-v1.md')==BODY_REPORT_SHA
    r=load(RUN/'public-body-receipt-v1.json')
    assert r['verdict']=='accepted-with-explicit-delta' and r['inputs_unchanged']
    assert r['fixed_input_count']==236 and not r['required_blocking_repairs']
    assert r['approved_future_exact_scope']==load(RUN/'body-future-integration-scope-v1.json')
    assert r['required_reader_corrections']==load(CONTRACT/'reader-requirements-v1.json')
    b=load(RUN/'body-bindings-v1.json')
    assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
    s=load(RUN/'stabilized-contract-v1.json')
    for p,h in [(CONTRACT/'targets-v1.json',s['targets_sha256']),
        (CONTRACT/'targets-v1.lean.txt',s['headers_sha256']),
        (CONTRACT/'source-intent-v1.md',s['source_intent_sha256']),
        (RUN/'source-contract-receipt-v1.json',s['receipt_sha256']),
        (RUN/'source-contract-review-v1.md',s['report_sha256'])]: assert sha(p)==h,p
    for t in s['targets']: assert statement_hash(lean_declaration_header(PUBLIC,t['name']))==t['statement_hash']
    allowed={p.resolve() for p in READERS+[ROOT/'BanditRLProof.lean',ROOT/'Tests.lean']}
    for row in load(RUN/'body-review-inputs-v1.json')['rows']:
        p=Path(row['path'])
        if sha(p)==row['sha256']: continue
        assert integrated and p.resolve() in allowed,p
        rel=p.resolve().relative_to(ROOT).as_posix()
        assert hashlib.sha256(baseline(rel)).hexdigest()==row['sha256']
    return r

def fixed_integrated():
    body_fixed(True)
    for rel,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingAECausal\n'),
        ('Tests.lean',b'\nimport Tests.OnlineGuessingAECausalCanary\n')]:
        assert (ROOT/rel).read_bytes()==baseline(rel)+addition
    proposal=load(RUN/'reader-proposal-v1.json')
    bound=load(RUN/'reader-integration-bindings-v1.json')
    assert sha(RUN/'reader-proposal-v1.json')==bound['reader_proposal_sha256']
    for label in ['readings','highlights','chapters']:
        old=json.loads(baseline('website/content/'+label+'.json').decode('utf8'))
        new=load(ROOT/'website/content'/(label+'.json'))
        assert set(old)==set(new)
        assert {k:v for k,v in old.items() if k!=label}=={k:v for k,v in new.items() if k!=label}
        if label=='highlights':
            assert new[label]==old[label]+proposal['notes']
            for t in load(CONTRACT/'targets-v1.json')['targets']:
                assert sum(n['full_name']==t['name'] for n in new[label])==1
        else:
            assert len(old[label])==len(new[label])
            for a,b in zip(old[label],new[label]):
                if a['slug']!=ROUTE: assert a==b
                elif label=='readings':
                    assert {k:v for k,v in a.items() if k!='source_theorems'}=={k:v for k,v in b.items() if k!='source_theorems'}
                    assert b['source_theorems']==a['source_theorems']+[proposal['card']]
                else:
                    allowed={'completion_blockers','open_gaps'}
                    assert {k:v for k,v in a.items() if k not in allowed}=={k:v for k,v in b.items() if k not in allowed}
                    for k in allowed: assert b[k]==a[k]+[proposal['boundary']]
    assert load(MANIFEST)['id']==TASK
    assert load(MANIFEST)['declarations']==[t['name'] for t in load(CONTRACT/'targets-v1.json')['targets']]
    assert load(MANIFEST)['affected_files']==[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS]
    return True
