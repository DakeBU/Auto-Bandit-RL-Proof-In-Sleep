from common_integrated_v1 import *
fixed_integrated()
# Track only the owned new Lean source before the existing harness's tracked source scan.
gate('track-own-canary-before-harness-v1','git','add','--',CANARY)
gate('combined-root-build-v1','lake','build','BanditRLProof')
gate('combined-Tests-build-v1','lake','build','Tests')
gate('combined-full-harness-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
fixed_integrated()
write(RUN/'combined-gates-v1.json',dict(public_files_sha256={p.as_posix():sha(p) for p in MODULES},
    canary_sha256=sha(CANARY),source_pins={p:sha(p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    actual_commands=['lake build BanditRLProof','lake build Tests','python tools/bandit.py check'],actual_exit_codes=[0,0,0],
    own_canary_tracked_before_harness=True,contributor_and_site_and_FINAL_pending=True,
    five_source_audits_still_pending_FINAL_native=True,new_production_proofs=0,chapter_complete=False,goal_complete=False))
