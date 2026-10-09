from common import *
fixed()
r = load(RUN / 'canary-BODY-publication-review-v1.json')
assert r['materialization_verdict'] == 'rejected' and r['BODY_verdict'] == 'accepted-with-explicit-delta'
event('reader-repair-native-v2', 'repair', dict(
    rejected_review_sha256=sha(RUN / 'canary-BODY-publication-review-v1.json'),
    versioned_repair_sha256=sha(RUN / 'reader-wording-repair-v2.json'),
    target_revision=False, production_and_Test_unchanged=True,
    exact_future_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v2.json'),
    scope='Required R9/L1 minimum-vs-minimizer reader wording repair, no actual materialization; distinct re-review pending.',
    source_container_closed=False, chapter_complete=False, goal_complete=False))
fixed()
