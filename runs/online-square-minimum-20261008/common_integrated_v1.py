from common_reviewed_v1 import *

ROUTE = 'online-foundations'
PRE = 'BanditRL.OnlineLearning.'
TEST = 'Tests.OnlineSquareMinimum.'
MANIFEST = Path('research-wiki/contribution-contracts/online-square-minimum-20261008.json')

def original(path):
    return load(RUN / 'snapshots' / (path.replace('/', '--') + '.raw'))

def body_fixed():
    headers_fixed(6)
    bindings = load(RUN / 'body-bindings-v1.json')
    assert sha(PUBLIC) == bindings['public_sha256'] and sha(CANARY) == bindings['canary_sha256']
    receipt = reviewer_receipt('public-body-receipt-v1.json')
    assert receipt['required_reader_corrections'] == load(RUN / 'stabilized-contract-v1.json')['original_reader_requirements']
    reviewed = {r['path']: r.get('sha256', r.get('sha256_raw_bytes')) for r in receipt['reviewed_files']}
    inputs = load(RUN / 'BODY-review-inputs-v1.json')
    assert receipt['fixed_input_count'] == inputs['fixed_input_count'] == 362
    for row in inputs['rows']:
        assert sha(row['path']) == row['sha256'] == reviewed[row['path']], row['path']

def fixed_integrated():
    body_fixed()
    for p, addition in [('BanditRLProof.lean', b'\nimport BanditRLProof.OnlineSquareMinimum\n'),
                        ('Tests.lean', b'\nimport Tests.OnlineSquareMinimumCanary\n')]:
        assert Path(p).read_bytes() == (RUN / 'snapshots' / (p + '.raw')).read_bytes() + addition, p
    before, after = original('website/content/readings.json'), load('website/content/readings.json')
    assert len(before['readings']) == len(after['readings'])
    for old, new in zip(before['readings'], after['readings']):
        if old['slug'] != ROUTE: assert old == new
        else:
            assert len(old['source_theorems']) == 10 and len(new['source_theorems']) == 11
            assert new['source_theorems'][:10] == old['source_theorems']
            assert {k:v for k,v in old.items() if k != 'source_theorems'} == {k:v for k,v in new.items() if k != 'source_theorems'}
    before, after = original('website/content/highlights.json'), load('website/content/highlights.json')
    assert after['highlights'][:len(before['highlights'])] == before['highlights']
    assert len(after['highlights']) == len(before['highlights']) + 6
    assert {k:v for k,v in after.items() if k != 'highlights'} == {k:v for k,v in before.items() if k != 'highlights'}
    assert all(x['full_name'].startswith(PRE) and not x['featured'] for x in after['highlights'][len(before['highlights']):])
    before, after = original('website/content/chapters.json'), load('website/content/chapters.json')
    assert len(before['chapters']) == len(after['chapters'])
    for old, new in zip(before['chapters'], after['chapters']):
        if old['slug'] != ROUTE: assert old == new
        else:
            assert new['module_globs'] == old['module_globs'] + [PUBLIC.as_posix()]
            changed = {'completion_blockers', 'open_gaps', 'module_globs'}
            assert {k:v for k,v in old.items() if k not in changed} == {k:v for k,v in new.items() if k not in changed}
