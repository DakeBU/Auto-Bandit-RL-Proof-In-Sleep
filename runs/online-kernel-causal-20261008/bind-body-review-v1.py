from common_canary_v1 import *

canary_fixed()
r = load(RUN/'public-body-receipt-v1.json')
assert sha(RUN/'public-body-receipt-v1.json') == '64d55a6fb4aedbd71b96ee272de38325e1ee429ead0d1f19ad88a212307017bc'
assert sha(RUN/'public-body-review-v1.md') == 'd3f89001487ff886ed1d7aac04f997d4ce9d4e3149c6ecc0043f79b4f043c965'
assert r['verdict'] == 'accepted-with-explicit-delta' and r['inputs_unchanged']
assert r['fixed_input_count'] == 350 and not r['required_blocking_repairs']
assert r['approved_future_exact_scope'] == load(RUN/'body-future-integration-scope-v1.json')
assert r['required_reader_corrections'] == load(CONTRACT/'reader-requirements-v1.json')
rows = load(RUN/'body-review-inputs-v1.json')['rows']
assert all(sha(x['path']) == x['sha256'] for x in rows)
mutable = [ROOT/directory/(TASK+'.md') for directory in
    ['tasks','proof-obligations','conversion-windows','proof-blueprints']]+\
    [ROOT/'runs/trials.jsonl',ROOT/'runs/lifecycle_sessions.jsonl']
snapshots = []
for i,p in enumerate(mutable):
    snapshot = RUN/'snapshots'/('body-mutable-'+str(i)+'.raw')
    write(snapshot,p.read_bytes())
    snapshots.append(dict(path=p.as_posix(),snapshot=snapshot.as_posix(),sha256=sha(p)))
write(RUN/'body-review-authority-v1.json',dict(
    receipt_sha256=sha(RUN/'public-body-receipt-v1.json'),report_sha256=sha(RUN/'public-body-review-v1.md'),
    fixed_input_count=350,all_current_fixed_RAW_match=True,
    mutable_snapshots=snapshots,package_accepted=False,chapter_complete=False,goal_complete=False))
from common_body_v1 import body_fixed
body_fixed()
print('Separate favorable BODY350 authority bound, exact future integration permitted; package gates pending.',flush=True)
