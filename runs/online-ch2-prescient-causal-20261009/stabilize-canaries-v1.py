from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
fixed()
rp = RUN / 'BODY-canary-contract-review-v1.json'
r = load(rp)
assert sha(rp) == 'eee51ec204ea477f78ec8a9ebe77945681e19c7991c31499a78b42aec8bc16cf'
assert r['BODY_verdict'] == r['canary_CONTRACT_verdict'] == 'accepted-with-explicit-delta'
assert not r['required_repairs'] and sha(r['report']) == r['report_sha256']
for row in load(RUN / 'BODY-canary-contract-review-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
d = load(CONTRACT / 'canary-targets-draft-v1.json')
assert d['targets'] == r['allowed_new_Test_scope']['frozen_targets']
assert sha(PUBLIC) == r['production_sha256']
assert not (ROOT / 'Tests/OnlinePrescientBregmanCanary.lean').exists()
for t in d['targets']:
    assert statement_hash(t['exact_proposed_header']) == t['statement_hash']
    assert hashlib.sha256(t['exact_proposed_header'].encode('utf8')).hexdigest() == t['header_raw_sha256']
write(CONTRACT / 'canary-stabilized-v1.json', dict(stage='stabilized', targets=d['targets'],
    context_sha256=d['neutral_sha256'], context_supplement_sha256=d['neutral_context_supplement_sha256'],
    draft_sha256=sha(CONTRACT / 'canary-targets-draft-v1.json'), review_sha256=sha(rp),
    production_sha256=sha(PUBLIC), allowed_scope=r['allowed_new_Test_scope'],
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
event('proving-canaries-native-v1', 'proving', dict(
    contract_sha256=sha(CONTRACT / 'canary-stabilized-v1.json'), review_sha256=sha(rp),
    frozen_hashes=[t['statement_hash'] for t in d['targets']],
    selected_now=[t['declaration'] for t in d['targets'][2:]],
    scope='First two dependency-ready canary bodies: actual exponential nonattainment/absorbing none and interior-extension/boundary audit. Two distinct-loss and outside-center run canaries follow by readiness. No old file edits.',
    source_container_closed=False, chapter_complete=False, goal_complete=False))
fixed()
print('Four exact complete concrete contracts frozen, first two canary leaves selected.')
