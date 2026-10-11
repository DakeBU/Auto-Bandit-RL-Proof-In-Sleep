from common import *

plan_path = RUN/'root-integration-proposal-20261011-v1.json'
review = load(RUN/'fresh-canary-BODY-review-20261011-v1.json')
approval = review['root_import_proposal_review']
assert approval['verdict'] == 'accepted' and approval['blocking_repairs'] == []
assert sha(plan_path) == approval['approved_plan_raw_sha256']
assert review['blocking_repairs'] == [] and review['all_bound_inputs_unchanged']
for row in review['inputs']:
    assert sha(Path(row['path'])) == row['raw_sha256_after'], row['path']
plan = load(plan_path)
for row in plan['rows']:
    assert sha(Path(row['path'])) == row['before_sha256']
    assert sha(Path(row['after_snapshot'])) == row['after_sha256']
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
    assert sha(Path(row['path'])) == row['after_sha256']
write(RUN/'root-integration-applied-20261011-v1.json', dict(
    approved_plan_sha256=sha(plan_path),
    review_sha256=sha(RUN/'fresh-canary-BODY-review-20261011-v1.json'),
    rows=plan['rows'], exact_after_verified=True, goal='active',
    package_acceptance=False, chapter_acceptance=False))
print('Applied exact reviewed append-only root imports.', flush=True)
