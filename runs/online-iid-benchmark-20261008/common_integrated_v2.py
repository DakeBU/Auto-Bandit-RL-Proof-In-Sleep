from common_reviewed_v2 import *

ROUTE='online-foundations'
TEST='Tests.OnlineGuessingIIDBenchmark.'
MANIFEST=Path('research-wiki/contribution-contracts/online-iid-benchmark-20261008.json')

def original(path):
    return load(RUN/'snapshots'/(path.replace('/','--')+'.raw'))

def body_fixed():
    headers_fixed(8)
    b=load(RUN/'body-bindings-v2.json')
    assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
    r=reviewer_receipt('public-body-receipt-v2.json')
    assert r['required_reader_corrections']==load(RUN/'stabilized-contract-v2.json')['original_reader_requirements']
    reviewed={row['path']:row.get('sha256',row.get('sha256_raw_bytes')) for row in r['reviewed_files']}
    inputs=load(RUN/'BODY-review-inputs-v2.json')
    assert r['fixed_input_count']==inputs['fixed_input_count']==583
    for row in inputs['rows']:
        assert sha(row['path'])==row['sha256']==reviewed[row['path']],row['path']
    return r

def fixed_integrated():
    body_fixed()
    for p,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingIIDBenchmark\n'),
                       ('Tests.lean',b'\nimport Tests.OnlineGuessingIIDBenchmarkCanary\n')]:
        assert Path(p).read_bytes()==(RUN/'snapshots'/(p+'.raw')).read_bytes()+addition,p
    before,after=original('website/content/readings.json'),load('website/content/readings.json')
    assert len(before['readings'])==len(after['readings'])
    for old,new in zip(before['readings'],after['readings']):
        if old['slug']!=ROUTE: assert old==new
        else:
            assert len(old['source_theorems'])==11 and len(new['source_theorems'])==12
            assert new['source_theorems'][:11]==old['source_theorems']
            assert {k:v for k,v in old.items() if k!='source_theorems'}=={k:v for k,v in new.items() if k!='source_theorems'}
    before,after=original('website/content/highlights.json'),load('website/content/highlights.json')
    assert after['highlights'][:len(before['highlights'])]==before['highlights']
    assert len(after['highlights'])==len(before['highlights'])+8
    assert {k:v for k,v in after.items() if k!='highlights'}=={k:v for k,v in before.items() if k!='highlights'}
    assert all(x['full_name'].startswith(PRE) and not x['featured'] for x in after['highlights'][len(before['highlights']):])
    before,after=original('website/content/chapters.json'),load('website/content/chapters.json')
    assert len(before['chapters'])==len(after['chapters'])
    for old,new in zip(before['chapters'],after['chapters']):
        if old['slug']!=ROUTE: assert old==new
        else:
            assert new['module_globs']==old['module_globs']+[PUBLIC.as_posix()]
            changed={'completion_blockers','open_gaps','module_globs'}
            assert {k:v for k,v in old.items() if k not in changed}=={k:v for k,v in new.items() if k not in changed}
