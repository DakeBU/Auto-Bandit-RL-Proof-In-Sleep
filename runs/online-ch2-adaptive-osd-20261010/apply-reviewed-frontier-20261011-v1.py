from common import *

review_path = RUN/'fresh-frontier-delivery-review-20261011-v1.json'
assert sha(review_path) == '0d0cf7885a801b81d653fe41123ef1de8ac61989e87e882ba80c0103d88d4b6e'
review = load(review_path)
assert review['frontier_verdict'] == 'accepted' and review['frontier_blocking_repairs'] == []
plan_path = RUN/'frontier-supersession-proposal-20261011-v1.json'
assert sha(plan_path) == review['approved_frontier_plan_raw_sha256']
plan = load(plan_path)
for row in plan['evidence']:
    assert sha(row['path']) == row['sha256']
for row in plan['rows']:
    assert sha(row['path']) == sha(row['before_snapshot']) == row['before_sha256']
    assert sha(row['after_snapshot']) == row['after_sha256']
    assert Path(row['after_snapshot']).read_bytes().startswith(Path(row['before_snapshot']).read_bytes())
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
    assert sha(row['path']) == row['after_sha256']
write(RUN/'frontier-applied-20261011-v1.json', dict(
    plan=rows([plan_path])[0], review=rows([review_path])[0],
    exact_applied_rows=plan['rows'], old_bytes_preserved=True,
    package_acceptance=False, chapter_acceptance=False, goal='active'))
print('Applied reviewed four append-only task frontier updates.', flush=True)
