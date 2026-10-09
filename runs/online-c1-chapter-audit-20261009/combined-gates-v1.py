from common_proving_v2 import *
fixed()
PUBLIC=ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean'
CANARY=ROOT/'Tests/OnlineLearningChapterAuditCanary.lean'
assert sha(CANARY)==load(RUN/'chapter-canary-BODY-receipt-v1.json')['test_module_sha256']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').strip()
gate('combined-stage-reviewed-two-Lean-v1','git','add',PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix())
codes=[]
for label,args in [('combined-root-v1',['lake','build','BanditRLProof']),('combined-Tests-v1',['lake','build','Tests']),('combined-full-harness-v1',[sys.executable,'-B','-X','utf8','tools/bandit.py','check'])]:
    code=gate(label,*args,required=False);codes.append(code)
    if code:
        write(RUN/'combined-gates-failure-v1.json',dict(actual_exit_codes=codes,failed=label,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),chapter_complete=False,goal_complete=False))
        raise AssertionError('Actual gate failed; preserve compiler/test log and repair '+label)
fixed()
assert sha(CANARY)==load(RUN/'chapter-canary-BODY-receipt-v1.json')['test_module_sha256']
write(RUN/'combined-gates-v1.json',dict(actual_exit_codes=codes,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},exact_two_reviewed_Lean_files_staged_before_harness=True,commands_finished_zero=True,compiler_test_logs_require_separate_inspection=True,current_site_FINAL_native_delivery_pending=True,chapter_complete=False,goal_complete=False))
print('Three real commands exited0; actual full logs must be inspected before acceptance.',flush=True)
