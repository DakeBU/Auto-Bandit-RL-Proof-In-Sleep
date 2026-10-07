from common_reviewed_v1 import *
reviewed_fixed()
assert load(RUN/'all-nine-focused-build-v2-exit.json')['exit_code']==0
write(RUN/'public-candidate-body-v1.lean.raw',PUBLIC.read_bytes())
write(RUN/'public-canary-input-v1.lean.raw',CANARY.read_bytes())
gate('public-canary-build-v1','lake','build','Tests.OnlineNoRegretSemanticsCanary')
write(RUN/'public-canary-build-summary-v1.json',dict(status='actual focused canary Lean build passed',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),named_canary_proofs=15,test_definitions=1,negative_limit_minus_one=True,actual_mean_negative_normalized_T2='-7/8',obstruction_actual_losses=[0,2,-2,4],obstruction_normalized_T2=-1,obstruction_normalized_T3=0,actual_nonempty_same_process_strict_separation=True,body_kernel_type_and_integrated_gates_pending=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
reviewed_fixed()
