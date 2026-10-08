from common_integrated_v1 import *
fixed_integrated()
# Only new own Lean sources are staged before the harness's anonymous-source allowlist gate.
# This does not commit or assert any gate outcome.
gate('stage-own-Lean-source-v1','git','-c','core.autocrlf=false','add','--',PUBLIC,CANARY)
gate('combined-root-v1','lake','build','BanditRLProof')
gate('combined-Tests-v1','lake','build','Tests')
gate('full-harness-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
fixed_integrated()
write(RUN/'combined-gates-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    source_pins={p:sha(p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    actual_commands=['lake build BanditRLProof','lake build Tests','python tools/bandit.py check'],
    actual_exit_codes=[load(RUN/(n+'-exit.json'))['exit_code'] for n in
        ['combined-root-v1','combined-Tests-v1','full-harness-v1']],
    own_new_sources_tracked_before_harness=True,FINAL_site_native_PR_pending=True,
    five_oldmain_contributor_audits='REQUIRED, notwaived',chapter_complete=False,goal_complete=False))
print('Actual sharedroot/Tests/fullharness passed with oldBandit andnewBook together; othergatespending.')
