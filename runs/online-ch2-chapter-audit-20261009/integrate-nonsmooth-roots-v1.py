from lower_common_v1 import *

reviewed();headers(3)
assert sha(RUN/'nonsmooth-canary-publication-review-v1.json')=='ac12e81d5ea3299b941237589ebad74fd7d0ea6ca0a58ae78069fdb1f66b590c'
r=load(RUN/'nonsmooth-canary-publication-review-v1.json')
assert r['canary_contract_verdict']==r['canary_body_verdict']=='accepted'
assert r['reader_proposal_verdict']=='rejected'
for row in r['raw_input_checks']:
    assert sha(row['path'])==row['before_sha256']==row['after_sha256']
plan=load(CONTRACT/'nonsmooth-exact-import-plan-v1.json')
assert r['approved_future_exact_scope']['exact_root_and_Test_imports_only']==plan
for p in plan['rows']:
    target=Path(p['path']);before=Path(p['snapshot']).read_bytes()
    assert target.read_bytes()==before and sha(target)==p['baseline_sha256']
    raw=before+p['append_exact_utf8'].encode('utf8')
    assert hashlib.sha256(raw).hexdigest()==p['permitted_result_sha256']
    target.write_bytes(raw)
write(RUN/'nonsmooth-root-integration-v1.json',dict(
    phase='Separate approved exact root/Test import integration only',
    actual_canary_review_sha256=sha(RUN/'nonsmooth-canary-publication-review-v1.json'),
    applied_exact_import_plan_sha256=sha(CONTRACT/'nonsmooth-exact-import-plan-v1.json'),
    old_root_raw_prefixes_preserved=True,reader_v1_rejected_and_not_applied=True,
    new_stage_guard='common_nonsmooth_roots_v1.py',old_guard_not_modified=True,
    current_root_Tests_harness_not_yet_passed=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
from common_nonsmooth_roots_v1 import fixed as root_fixed
root_fixed()
print('Only two independently approved exact root appends applied; wrong reader proposal unapplied.')
