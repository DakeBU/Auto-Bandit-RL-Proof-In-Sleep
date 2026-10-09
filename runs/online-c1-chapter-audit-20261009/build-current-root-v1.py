from common_proving_v2 import *
fixed()
gate('shared-root-general-init-v1','lake','build','BanditRLProof')
fixed()
write(RUN/'shared-root-general-init-v1.json',dict(actual_root_build_zero=True,root_raw_sha256=sha(ROOT/'BanditRLProof.lean'),new_production_sha256=sha(ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean'),scope='Shared BanditRLProof root with unchanged old Bandit/Book library and four exact new producers',Tests_gate_pending_new_canary=True,full_harness_pending=True,chapter_complete=False,goal_complete=False))
print('Current shared production root compiled; new chapter canary/Tests/harness still pending.',flush=True)
