from common_v1 import *
from common_reviewed_v2 import REVIEW_REPORT_SHA, REVIEW_RECEIPT_SHA
from collections import Counter

ROUTE='online-foundations'
TEST='Tests.OnlineGuessingRandomizedIID.'
MANIFEST=Path('research-wiki/contribution-contracts/online-randomized-iid-20261008.json')
OWN_METADATA=[Path(d)/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations',
    'proof-blueprints','research-wiki/retrieval-index']]


def original(path):
    p=RUN/'snapshots'/('CONTRACT-reviewed--'+path.replace('/','--')+'.raw')
    return load(p)


def reviewer_receipt(name):
    r=load(RUN/name)
    assert r['actor']['task']=='/root/source_reviewer'
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert r['before_after_raw_hashes_match']
    for key in ['required_repairs','required_blocking_repairs','required_mathematical_repairs',
            'required_metadata_repairs','required_blocking_reader_repairs']:
        assert not r.get(key,[]),(key,r.get(key))
    p=r['report']['path'] if isinstance(r['report'],dict) else r['report']
    expected=r.get('report_sha256')
    if expected is None: expected=r['report'].get('sha256',r['report'].get('sha256_raw_bytes'))
    assert expected and sha(p)==expected
    return r


def headers_body_fixed():
    fixed()
    assert sha(RUN/'source-contract-review-v2.md')==REVIEW_REPORT_SHA
    assert sha(RUN/'source-contract-receipt-v2.json')==REVIEW_RECEIPT_SHA
    b=load(RUN/'body-bindings-v2.json')
    assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
    context=(CONTRACT/'public-context-v2.lean').read_text(encoding='utf8')
    text=PUBLIC.read_text(encoding='utf8')
    assert text.startswith(context[:context.index('end BanditRL.OnlineLearning')])
    for row in load(CONTRACT/'targets-v2.json')['rows']:
        assert hashlib.sha256(row['header'].encode('utf8')).hexdigest()==row['header_sha256']
        assert text.count(row['header']+' := by')==1
    resolutions={r['live_path']:r for r in load(RUN/'CONTRACT-original-input-resolutions-v2.json')}
    for row in load(RUN/'source-review-inputs-v2.json')['rows']:
        p=Path(row['path'])
        if sha(p)==row['sha256']: continue
        resolution=resolutions.get(p.as_posix())
        assert resolution and sha(resolution['snapshot'])==row['sha256'],p
        if p in OWN_METADATA or p.as_posix() in ['BanditRLProof.lean','Tests.lean']:
            assert p.read_bytes().startswith(Path(resolution['snapshot']).read_bytes()),p
        elif p.as_posix()=='research-wiki/retrieval-index/local_lean_declarations.json':
            canonical=lambda r:json.dumps(r,sort_keys=True,ensure_ascii=False)
            old=Counter(map(canonical,load(resolution['snapshot'])['declarations']))
            now=Counter(map(canonical,load(p)['declarations']))
            assert all(now[k]>=v for k,v in old.items()),p
        else:
            assert p==MANIFEST or p.as_posix() in ['website/content/readings.json',
                'website/content/highlights.json','website/content/chapters.json'],p
            # This finite reviewed permission is checked by body_fixed and exact integration preservation below.
            assert (RUN/'public-body-receipt-v2.json').exists()


def body_fixed():
    headers_body_fixed()
    r=reviewer_receipt('public-body-receipt-v2.json')
    assert r['required_reader_corrections']==load(CONTRACT/'reader-requirements-v2.json')
    assert r['permitted_future_integration'], 'No authority for source/readers/own manifest metadata edits.'
    inputs=load(RUN/'BODY-review-inputs-v2.json')
    assert r['fixed_input_count']==inputs['fixed_input_count']==1582
    reviewed={Path(x['path']).resolve().as_posix():x.get('sha256',x.get('sha256_raw_bytes')) for x in r['reviewed_files']}
    for row in inputs['rows']:
        p=Path(row['path'])
        assert reviewed[p.resolve().as_posix()]==row['sha256'],p
        if sha(p)==row['sha256']: continue
        assert p.resolve() in {x.resolve() for x in OWN_METADATA},p
        snapshot=RUN/'snapshots'/('BODY-reviewed--'+p.relative_to(ROOT).as_posix().replace('/','--')+'.raw')
        assert sha(snapshot)==row['sha256'] and p.read_bytes().startswith(snapshot.read_bytes()),p
    return r


def fixed_integrated():
    body_fixed()
    for p,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingRandomizedIID\n'),
            ('Tests.lean',b'\nimport Tests.OnlineGuessingRandomizedIIDCanary\n')]:
        before=(RUN/'snapshots'/('CONTRACT-reviewed--'+p+'.raw')).read_bytes()
        assert Path(p).read_bytes()==before+addition,p
    before,after=original('website/content/readings.json'),load('website/content/readings.json')
    assert {k:v for k,v in before.items() if k!='readings'}=={k:v for k,v in after.items() if k!='readings'}
    assert len(before['readings'])==len(after['readings'])
    for old,new in zip(before['readings'],after['readings']):
        if old['slug']!=ROUTE: assert old==new
        else:
            assert len(old['source_theorems'])==12 and len(new['source_theorems'])==13
            assert new['source_theorems'][:12]==old['source_theorems']
            assert {k:v for k,v in old.items() if k!='source_theorems'}=={k:v for k,v in new.items() if k!='source_theorems'}
    before,after=original('website/content/highlights.json'),load('website/content/highlights.json')
    assert after['highlights'][:len(before['highlights'])]==before['highlights']
    assert len(after['highlights'])==len(before['highlights'])+7
    assert {k:v for k,v in before.items() if k!='highlights'}=={k:v for k,v in after.items() if k!='highlights'}
    expected=[r['name'] for r in load(CONTRACT/'targets-v2.json')['rows']]
    additions=after['highlights'][len(before['highlights']):]
    assert [x['full_name'] for x in additions]==expected
    assert all(not x['featured'] and x['chapter']==ROUTE for x in additions)
    before,after=original('website/content/chapters.json'),load('website/content/chapters.json')
    assert {k:v for k,v in before.items() if k!='chapters'}=={k:v for k,v in after.items() if k!='chapters'}
    assert len(before['chapters'])==len(after['chapters'])
    for old,new in zip(before['chapters'],after['chapters']):
        if old['slug']!=ROUTE: assert old==new
        else:
            assert new['module_globs']==old['module_globs']+[PUBLIC.as_posix()]
            changed={'module_globs','completion_blockers','open_gaps'}
            assert {k:v for k,v in old.items() if k not in changed}=={k:v for k,v in new.items() if k not in changed}
    m=load(MANIFEST)
    assert m['schema_version']=='2.0' and m['id']==TASK
    assert m['declarations']==expected+[PRE+'privateSeedPastInformation']
    assert m['semantic_roundtrip']['required'] and m['semantic_roundtrip']['source_reviewer']=='/root/source_reviewer'
