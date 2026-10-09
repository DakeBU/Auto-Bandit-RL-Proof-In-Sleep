from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash

fixed()
rp = RUN / 'BODY-canary-contract-review-v1.json'
assert sha(rp) == '6531929781a4a12440ac1bbbf9b31d0b1bb982bcaee2d9b1a22a0eccd493d117'
r = load(rp)
assert r['BODY_verdict'] == r['canary_CONTRACT_verdict'] == 'accepted-with-explicit-delta'
assert not r['required_repairs']
assert sha(r['report']) == r['report_sha256']
for row in load(RUN / 'BODY-canary-contract-review-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
d = load(CONTRACT / 'canary-targets-draft-v1.json')
assert d['targets'] == r['allowed_new_Test_scope']['targets']
assert sha(PUBLIC) == r['production_sha256']
assert not (ROOT / 'Tests/OnlineBregmanExtendedCanary.lean').exists()
for t in d['targets']:
    assert statement_hash(t['exact_proposed_header']) == t['statement_hash']
    assert hashlib.sha256(t['exact_proposed_header'].encode('utf8')).hexdigest() == t['header_raw_sha256']
write(CONTRACT / 'canary-stabilized-v1.json', dict(
    stage='stabilized', targets=d['targets'], context_sha256=d['neutral_sha256'],
    draft_sha256=sha(CONTRACT / 'canary-targets-draft-v1.json'), review_sha256=sha(rp),
    production_sha256=sha(PUBLIC), allowed_scope=r['allowed_new_Test_scope'],
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
event('proving-canaries-native-v1', 'proving', dict(
    contract_sha256=sha(CONTRACT / 'canary-stabilized-v1.json'), review_sha256=sha(rp),
    frozen_hashes=[t['statement_hash'] for t in d['targets']],
    scope='Only two exact infinity Test conjunctions and explicit local helpers/imports; no old file edits.',
    source_container_closed=False, chapter_complete=False, goal_complete=False))
fixed()
print('Two exact infinity canary types stabilized; native/raw hashes separately checked.')
