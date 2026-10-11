from common import *

plan_path = RUN/'exact-integration-proposal-20261011-v5.json'
review_path = RUN/'fresh-exact-integration-review-20261011-v5.json'
assert sha(review_path) == 'a3528d6879e1ea091a952827dd7fa86fa1c9b4f733d3bec4349616c1b41806fc'
review = load(review_path)
assert review['verdict'] == 'accepted' and review['blocking_repairs'] == []
assert review['approved_plan_raw_sha256'] == sha(plan_path)
plan = load(plan_path)
assert review['approved_rows'] == plan['rows']
for group in ['production_and_tests','semantic_reviews','prospective_manifest','reader_proposal','mapping']:
    for row in plan[group]:
        assert sha(row['path']) == row['sha256'], row['path']
assert sha(PDF) == PDF_SHA
for row in plan['rows']:
    assert sha(row['before_snapshot']) == row['before_sha256']
    assert sha(row['after_snapshot']) == row['after_sha256']
    expected = row['after_sha256'] if Path(row['path']).name in ['BanditRLProof.lean','Tests.lean'] else row['before_sha256']
    assert sha(row['path']) == expected, row['path']
destination = ROOT/plan['new_manifest']
assert not destination.exists()
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_bytes(Path(plan['prospective_manifest'][0]['path']).read_bytes())
for row in plan['rows']:
    assert sha(row['path']) == row['after_sha256']
assert sha(destination) == plan['prospective_manifest'][0]['sha256']
write(RUN/'publication-applied-20261011-v1.json', dict(
    plan=rows([plan_path])[0], review=rows([review_path])[0],
    exact_applied_rows=plan['rows'], new_manifest=rows([destination])[0],
    roots_previously_applied=True, package_acceptance=False,
    chapter_acceptance=False, main_updated=False, deployed=False, goal='active'))
print('Applied independently approved exact reader/Book/manifest snapshots.', flush=True)
