from common_body_v1 import *

fixed_integrated()
gate('track-own-Lean-before-harness-v1','git','add','--',PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix())
gate('combined-root-build-v1','lake','build','BanditRLProof')
gate('combined-Tests-build-v1','lake','build','Tests')
gate('combined-full-harness-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
fixed_integrated()
write(RUN/'combined-gates-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    actual_commands=['lake build BanditRLProof','lake build Tests','python tools/bandit.py check'],
    actual_exit_codes=[0,0,0],own_public_and_canary_tracked_before_harness=True,
    new_production_proofs=5,new_named_canary_proofs=13,
    contributor_site_final_native_delivery_pending=True,chapter_complete=False,goal_complete=False))
print('Combined Lean root/Tests/full harness actual passed; remaining package gates pending.',flush=True)
