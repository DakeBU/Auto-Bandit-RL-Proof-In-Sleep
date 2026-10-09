from publication_guard_v1 import *
fixed()
rpath = RUN / 'render-repair-review-v3.json'
r = load(rpath)
assert r['verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert r['materialization_verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert not r['required_repairs'] and r['exact_math_delta_only']
assert sha(r['report']) == r['report_sha256']
assert sha(RUN / 'render-repair-review-inputs-v3.json') == r['input_manifest_sha256']
for row in load(RUN / 'render-repair-review-inputs-v3.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
planpath = CONTRACT / 'exact-publication-plan-v3.json'
plan = load(planpath)
assert sha(planpath) == r['approved_plan_sha256'] and plan['rows'] == r['approved_five_rows']
oldplan = load(CONTRACT / 'exact-publication-plan-v2.json')
old = load(ROOT / 'website/content/highlights.json')
new = load(RUN / 'publication-after-highlights-v3.json')
changes = []
def compare(a, b, trail=()):
    assert type(a) == type(b), trail
    if isinstance(a, dict):
        assert a.keys() == b.keys(), trail
        for key in a:
            compare(a[key], b[key], trail + (key,))
    elif isinstance(a, list):
        assert len(a) == len(b), trail
        for i, (x, y) in enumerate(zip(a, b)):
            compare(x, y, trail + (i,))
    elif a != b:
        changes.append(trail)
compare(old, new)
assert len(changes) == 1 and changes[0][0] == 'highlights' and changes[0][-1] == 'math'
i = changes[0][1]
assert old['highlights'][i]['full_name'] == new['highlights'][i]['full_name'] == 'BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained'
write(RUN / 'render-repair-binding-v3.json', dict(review_sha256=sha(rpath), plan_sha256=sha(planpath),
    original_canary_BODY_review_sha256=sha(RUN / 'canary-BODY-publication-review-v1.json'),
    original_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v2.json'),
    production_sha256=sha(PUBLIC), canary_sha256=sha(CANARY), exact_changed_JSON_field=changes[0],
    source_Lean_contracts_unchanged=True, whole_Goal_status='ACTIVE'))
for a, b in zip(oldplan['rows'], plan['rows']):
    assert a['path'] == b['path'] and a['before_sha256'] == b['before_sha256']
    assert sha(a['path']) == a['after_sha256'] and sha(b['after_snapshot']) == b['after_sha256']
    if a['after_sha256'] != b['after_sha256']:
        assert b['path'] == (ROOT / 'website/content/highlights.json').as_posix()
        Path(b['path']).write_bytes(Path(b['after_snapshot']).read_bytes())
from publication_guard_v2 import fixed as repaired_fixed
repaired_fixed()
write(RUN / 'render-repair-materialized-v3.json', dict(actual_exact_one_new_math_field=True,
    full_harness_applicable_to_unchanged_Lean_sha256=sha(RUN / 'full-harness-inspected-v1.json'),
    fresh_full_harness_rerun_claim=False, repaired_site_browser_FINAL_pending=True,
    original_failure_retained=True, whole_Goal_status='ACTIVE'))
repaired_fixed()
print('Exact reviewed one-field rendering repair materialized; second clean site/browser required.')
