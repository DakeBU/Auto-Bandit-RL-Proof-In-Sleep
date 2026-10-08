from common_reviewed_v1 import *
BODY_SHA='ec526a456d3db1c4c6bbf7ba78e67dc4853ef4529fce8c48dbf7fbdf13e3d0c7'
BODY_REPORT_SHA='24d240b8c277a2f662bae460ada072985dd29f3d1c9be07c052b3c306a59b830'
ROUTE='online-foundations'
MANIFEST=Path('research-wiki/contribution-contracts/online-iid-success-20261008.json')
READER_FILES=[Path('BanditRLProof.lean'),Path('Tests.lean'),Path('website/content/readings.json'),
    Path('website/content/highlights.json'),Path('website/content/chapters.json')]

def original(p):
    return RUN/'snapshots'/('BODY-integrate-baseline--'+Path(p).as_posix().replace('/','--')+'.raw')

def body_fixed(integrated=False):
    headers_fixed(4)
    assert sha(RUN/'public-body-receipt-v1.json')==BODY_SHA
    assert sha(RUN/'public-body-review-v1.md')==BODY_REPORT_SHA
    r=load(RUN/'public-body-receipt-v1.json')
    assert r['verdict']=='accepted-with-explicit-delta' and r['inputs_unchanged']
    assert not r['required_blocking_repairs']
    assert r['future_integration_scope_verdict']['verdict']=='accepted-with-explicit-delta'
    assert r['reader_requirements']==load(RUN/'stabilized-contract-v1.json')['reader_requirements']
    b=load(RUN/'body-bindings-v1.json')
    assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
    allowed={p.resolve() for p in READER_FILES+APPEND_METADATA}
    for p,h in load(RUN/'body-review-inputs-v1.json')['fixed_inputs'].items():
        p=Path(p)
        if sha(p)==h: continue
        assert integrated and p.resolve() in allowed,p
        rel=p.resolve().relative_to(ROOT)
        snapshot=(original(rel) if rel in READER_FILES else
            RUN/'snapshots'/('BODY-current--'+rel.as_posix().replace('/','--')+'.raw'))
        assert sha(snapshot)==h,p
        if rel in APPEND_METADATA:
            assert p.read_bytes().startswith(snapshot.read_bytes())
            # Prefix preservation alone is NOT permission for an arbitrary suffix.
            records=load(RUN/'owned-suffix-bindings-v1.json')['suffixes']
            suffix=p.read_bytes()[len(snapshot.read_bytes()):]
            assert hashlib.sha256(suffix).hexdigest()==records[rel.as_posix()]['sha256'],p
    return r

def fixed_integrated():
    body_fixed(True)
    for p,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingIIDSuccess\n'),
        ('Tests.lean',b'\nimport Tests.OnlineGuessingIIDSuccessCanary\n')]:
        assert Path(p).read_bytes()==original(p).read_bytes()+addition,p
    old,new=load(original('website/content/readings.json')),load('website/content/readings.json')
    assert set(old)==set(new) and old['edition_note']==new['edition_note']
    assert len(old['readings'])==len(new['readings'])
    for a,b in zip(old['readings'],new['readings']):
        if a['slug']!=ROUTE: assert a==b
        else:
            assert {k:v for k,v in a.items() if k!='source_theorems'}=={k:v for k,v in b.items() if k!='source_theorems'}
            assert b['source_theorems'][:-1]==a['source_theorems'] and len(b['source_theorems'])==14
    old,new=load(original('website/content/highlights.json')),load('website/content/highlights.json')
    assert set(old)==set(new) and new['highlights'][:-4]==old['highlights']
    assert [n['full_name'] for n in new['highlights'][-4:]]==[r['name'] for r in load(CONTRACT/'targets-v1.json')['targets']]
    old,new=load(original('website/content/chapters.json')),load('website/content/chapters.json')
    assert set(old)==set(new) and len(old['chapters'])==len(new['chapters'])
    for a,b in zip(old['chapters'],new['chapters']):
        if a['slug']!=ROUTE: assert a==b
        else:
            keys={'module_globs','completion_blockers','open_gaps'}
            assert {k:v for k,v in a.items() if k not in keys}=={k:v for k,v in b.items() if k not in keys}
            assert b['module_globs']==a['module_globs']+[PUBLIC.as_posix()]
            for k in ['completion_blockers','open_gaps']:
                assert b[k][:-1]==a[k] and b[k][-1]==load(RUN/'reader-proposal-v1.json')['boundary']
    assert load(MANIFEST)['id']==TASK
    return True
