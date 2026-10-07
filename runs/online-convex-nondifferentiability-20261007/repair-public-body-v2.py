"""Focused constant-derivative API repair, immutable targets and original failed body."""
from common_v4 import *
fixed(False,True);assert load(RUN/'public-body-v1-01-exit.json')['exit_code']==1
write(RUN/'leaves/public-body-failed-v1.lean',PUBLIC.read_bytes())
text=PUBLIC.read_text(encoding='utf-8');assert 'differentiableAt_const.add' in text
text=text.replace('differentiableAt_const.add','(differentiableAt_const x).add').replace('simp [PiLp.single_apply]','simp')
PUBLIC.write_bytes(text.encode());fixed(False,True)
write(RUN/'body-repair-v2.json',dict(actual_failed_attempt='public-body-v1-01',error_signature='Unknown constant differentiableAt_const.add',repair='Supply actual constant x to differentiableAt_const before .add; remove unused segment simp argument.',frozen_headers_and_definition_unchanged=True,source_contract_unchanged=True,mathematical_target_repairs=[],proof_route_unchanged=True,old_failed_body_raw=(RUN/'leaves/public-body-failed-v1.lean').as_posix(),old_failed_body_sha256=sha(RUN/'leaves/public-body-failed-v1.lean')))
native('failed-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','proof','--status','failed','--run-id',RUN.name,'--attempt-id','NONDIFF-BODY-V1','--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['convex_nondifferentiable_segment'],'--verifier-evidence',RUN/'public-body-v1-01.log','--harness','hierarchical','--progress-class','no-progress','--error-signature','Unknown constant differentiableAt_const.add','--notes','Actual publicbody V1 failed curve derivative API; same frozen source/targets, focused constant-argument repair only, no strategy/target weakening.')
event('repair',dict(body_attempt='NONDIFF-BODY-V1',repair=(RUN/'body-repair-v2.json').as_posix(),target_unchanged=True),attempt='body-v2')
print('Actual failed body preserved; focused same-route API repair with all4frozen native headers unchanged.')
