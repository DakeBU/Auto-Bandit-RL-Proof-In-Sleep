from publication_guard_v4 import *
fixed()
rpath = RUN/'contributor-repair-review-v1.json'
r = load(rpath)
assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and r['materialization_verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r['required_repairs'] and r['exact_affected_files_delta_only']
assert sha(r['report']) == r['report_sha256'] and sha(RUN/'contributor-repair-inputs-v1.json') == r['input_manifest_sha256']
for row in load(RUN/'contributor-repair-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
p = RUN/'contribution-after-range-ownership-v1.json'
assert sha(p) == r['approved_after_sha256']
old,new = load(CONTRIBUTION),load(p)
assert new['affected_files'] == old['affected_files'] + ['website/content/declaration-boundaries.json']
assert {k:v for k,v in old.items() if k != 'affected_files'} == {k:v for k,v in new.items() if k != 'affected_files'}
write(RUN/'contributor-repair-binding-v1.json',dict(review_sha256=sha(rpath), before_sha256=sha(CONTRIBUTION), after_sha256=sha(p),
    exact_only_affected_files_append=True, production_Test_config_generator_unchanged=True, whole_Goal_status='ACTIVE'))
CONTRIBUTION.write_bytes(p.read_bytes())
fixed()
print('Exact reviewed ownership append materialized; fresh contributor/site/browser pending.')
