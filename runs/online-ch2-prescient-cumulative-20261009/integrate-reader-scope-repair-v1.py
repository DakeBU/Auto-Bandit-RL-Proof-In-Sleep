from publication_guard_v3 import *
fixed()
review=load(RUN/'reader-scope-plan-review-v1.json')
assert review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']
assert sha(review['report'])==review['report_sha256']
assert review['input_manifest_sha256']==sha(RUN/'reader-scope-plan-inputs-v1.json')
for row in load(RUN/'reader-scope-plan-inputs-v1.json')['rows']: assert sha(row['path'])==row['sha256'],row['path']
mut=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','trials.jsonl','own-artifact-journal.md']]
write(RUN/'pre-reader-repair-native-exact-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mut]))
event('reader-scope-repair-native-v1','repair',dict(reason='Shared prose overrestricts arbitrary positive schedule divergence_sum;13 exact prose fields only.',proof_statement_change=False,source_container_closed=False,goal_complete=False))
plan=load(CONTRACT/'reader-scope-repair-plan-v1.json')
for row in plan['rows']:
    assert sha(row['path'])==row['before_sha256'] and sha(row['after_snapshot'])==row['after_sha256']
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
write(RUN/'reader-scope-repair-binding-v1.json',dict(review_sha256=sha(RUN/'reader-scope-plan-review-v1.json'),plan_sha256=sha(CONTRACT/'exact-publication-plan-v3.json'),exact_field_changes=13,source_statements_unchanged=True,original_SITEv1_and_reviews_retained=True,whole_Goal_status='ACTIVE'))
from publication_guard_v4 import fixed as repaired_fixed
repaired_fixed()
print('Only approved13 reader prose fields repaired; fresh site/pixels/FINAL pending.')
