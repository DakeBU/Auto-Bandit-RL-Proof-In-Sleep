from publication_guard_v3 import *
fixed()
failed=RUN/'candidate-full-diff-check-v1.json'
assert load(failed)['actual_exit']==2
out=base64.b64decode(load(failed)['stdout_base64']).decode('utf8')
rel=RUN.relative_to(ROOT).as_posix()+'/publication-director-v1.md'
assert out.count('trailing whitespace.')==1 and rel+':1: trailing whitespace.' in out
p=ROOT/rel; old=p.read_bytes()
assert old.endswith(b' \n') and old.count(b'\n')==1
for index in ['five-BODY-review-inputs-v1.json','publication-plan-review-inputs-v3.json']:
    row=next(r for r in load(RUN/index)['rows'] if r['path']==p.as_posix())
    assert row['sha256']==sha(p)
after=old[:-2]+b'\n'
write(RUN/'OWN-whitespace-exact-before-v1.json',dict(path=p.as_posix(),before_sha256=sha(p),before_raw_base64=base64.b64encode(old).decode('ascii'),after_sha256=hashlib.sha256(after).hexdigest(),exact_byte_delta='Delete precisely one space immediately before final LF; no other byte changes.',historical_review_inputs_resolve_to_exact_beforebytes=True,frozen_Lean_headers_bodies_and_reader_plan_unchanged=True,not_claiming_historical_input_currently_unchanged_after_format_repair=True,whole_Goal_status='ACTIVE'))
p.write_bytes(after)
write(RUN/'OWN-whitespace-repair-inspected-v1.json',dict(failed_actual_exit=2,failed_receipt_sha256=sha(failed),exact_before_receipt_sha256=sha(RUN/'OWN-whitespace-exact-before-v1.json'),repaired_path=p.as_posix(),current_after_sha256=sha(p),scope='Task-owned prose formatting only, within authorized OWN evidence. Original SHA-bound historical RAW preserved contemporaneously as base64, not overwritten without evidence. FINAL must inspect this explicit resolution; no new source/statement/body/reader weakening.',production_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),whole_Goal_status='ACTIVE'))
s=(RUN/'prepare-stage-v2.py').read_text(encoding='utf8').replace('-v1','-v2').replace('full-harness-inspected-v2.json','full-harness-inspected-v1.json')
write(RUN/'prepare-stage-v3.py',s)
s=(RUN/'commit-and-build-site-v2.py').read_text(encoding='utf8').replace('candidate-diff-audit-v1.json','candidate-diff-audit-v2.json').replace('candidate-stage-plan-v1.json','candidate-stage-plan-v2.json')
write(RUN/'commit-and-build-site-v3.py',s)
fixed()
print('One OWN prose trailing space repaired with exact historical RAW retained; no mathematical/publication target change. Whitespace gate rerun pending.')
