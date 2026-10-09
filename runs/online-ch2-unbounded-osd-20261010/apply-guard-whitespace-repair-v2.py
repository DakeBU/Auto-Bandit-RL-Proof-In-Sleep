from common import *
r=load(RUN/'guard-whitespace-repair-review-v2.json')
assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
for row in load(r['input_manifest'])['rows']:assert sha(row['path'])==row['sha256'],row['path']
p=RUN/'guard-whitespace-exact-plan-v2.json';plan=load(p)
assert r['approved_plan_sha256']==sha(p)
for row in plan['transitions']:
    assert sha(row['path'])==row['before_sha256']
    assert sha(row['after_snapshot'])==row['after_sha256']
from publication_guard_v1 import fixed as before_fixed
before_fixed()
for row in plan['transitions']:Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
from publication_guard_v2 import fixed as after_fixed
after_fixed()
write(RUN/'guard-whitespace-repair-applied-v2.json',dict(approved_plan_sha256=sha(p),exact_transitions=plan['transitions'],source_Test_pins_unchanged=True,old_review_manifests_immutable=True,not_Lean_failure=True,site_build_pending=True))
print('Exact reviewed own guard/whitespace repair applied; old reviewed RAW preserved.',flush=True)
