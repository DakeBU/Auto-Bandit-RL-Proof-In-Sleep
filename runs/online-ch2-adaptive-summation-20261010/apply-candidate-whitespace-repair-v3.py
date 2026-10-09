from candidate_guard_v1 import *
from gate_receipt_guard_v3 import actual_gates_fixed, gate_binding_review_fixed
# Preserve complete original current scope before exact NEW OWN repair.
candidate_fixed();gate_binding_review_fixed(after=False);actual_gates_fixed()
r=load(RUN/'candidate-whitespace-repair-review-v2.json')
assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
p=RUN/'candidate-whitespace-repair-plan-v2.json';assert sha(p)==r['approved_repair_plan_sha256']
for row in load(r['input_manifest'])['rows']: assert sha(row['path'])==row['sha256'],row['path']
for row in r['approved_helper_hashes']: assert sha(row['path'])==row['sha256'],row['path']
changed,bindings=exact_cached_scope()
write(RUN/'failed-stage-RAW-inspected-pre-repair-v3.json',dict(changed_paths=changed,all_staged_blobs=bindings,scope='Exact failed stage bytes preserved; no success claim.'))
for a in load(p)['rows']:
    assert sha(a['path'])==a['before_sha256']
    assert hashlib.sha256(base64.b64decode(a['before_raw_base64'])).hexdigest()==a['before_sha256']
    assert sha(a['after_snapshot'])==a['after_sha256']
for a in load(p)['rows']: Path(a['path']).write_bytes(Path(a['after_snapshot']).read_bytes())
import integration_guard_v2
integration_guard_v2.fixed()
gate_binding_review_fixed(after=True)
write(RUN/'candidate-whitespace-repair-applied-v3.json',dict(plan_sha256=sha(p),exact_rows=load(p)['rows'],production_sha256=sha(MODULE),Test_sha256=sha(TEST),scope='Five explicit NEW OWN whitespace transitions only. Full cached BASE whitespace still requires actual rerun.',chapter_complete=False,whole_Goal='active'))
