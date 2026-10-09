from publication_guard_v2 import *
fixed()
rp = RUN / 'catalogue-repair-review-v5.json'
r = load(rp)
assert r['verdict'] in ['accepted', 'accepted-with-explicit-delta'] and r['materialization_verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert not r['required_repairs'] and r['exact_boundary_delta_only']
assert sha(r['report']) == r['report_sha256']
assert sha(RUN / 'catalogue-repair-review-inputs-v5.json') == r['input_manifest_sha256']
for row in load(RUN / 'catalogue-repair-review-inputs-v5.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
planpath = CONTRACT / 'exact-publication-plan-v5.json'
plan = load(planpath)
assert sha(planpath) == r['approved_plan_sha256'] and plan['rows'] == r['approved_six_rows']
assert plan['allowed_old_mutations'] == len(plan['rows']) == 6
assert plan['rows'][:5] == load(CONTRACT / 'exact-publication-plan-v3.json')['rows']
row = plan['rows'][-1]
assert row['path'] == (ROOT / 'website/content/declaration-boundaries.json').as_posix()
assert sha(row['path']) == row['before_sha256'] == sha(row['before_snapshot'])
assert sha(row['after_snapshot']) == row['after_sha256']
old, new = load(row['path']), load(row['after_snapshot'])
assert old['schema_version'] == new['schema_version'] == 1 and new['entries'][:-1] == old['entries'] and len(new['entries']) == len(old['entries']) + 1
write(RUN / 'catalogue-repair-binding-v5.json', dict(review_sha256=sha(rp), plan_sha256=sha(planpath),
    original_canary_BODY_review_sha256=sha(RUN / 'canary-BODY-publication-review-v1.json'),
    prior_render_review_sha256=sha(RUN / 'render-repair-review-v3.json'),
    rejected_original_catalogue_review_sha256=sha(RUN / 'catalogue-repair-review-v4.json'),
    production_sha256=sha(PUBLIC), canary_sha256=sha(CANARY), old_entries_all_preserved=True,
    exact_only_new_entry=new['entries'][-1], whole_Goal_status='ACTIVE'))
Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
from publication_guard_v4 import fixed as repaired_fixed
repaired_fixed()
write(RUN / 'catalogue-repair-materialized-v5.json', dict(exact_one_config_entry=True,
    original_rejection_retained=True, production_Test_generator_unchanged=True,
    fresh_combined_site_browser_FINAL_pending=True, whole_Goal_status='ACTIVE'))
print('Reviewed exact frozen-definition range materialized; fresh combined/site/browser pending.')
