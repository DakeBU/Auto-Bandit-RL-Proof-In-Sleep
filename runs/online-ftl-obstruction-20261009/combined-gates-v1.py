from common_body_v2 import *
integrated_fixed()
assert not subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').strip()
gate('combined-stage-two-reviewed-Lean-v1','git','add',PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix())
codes=[]
for label,args in [('combined-root-v1',['lake','build','BanditRLProof']),
    ('combined-Tests-v1',['lake','build','Tests']),
    ('combined-full-harness-v1',[sys.executable,'-B','-X','utf8','tools/bandit.py','check'])]:
    code=gate(label,*args,required=False);codes.append(code)
    if code:
        write(RUN/'combined-gates-failure-v1.json',dict(actual_exit_codes=codes,failed=label,
            public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),package_accepted=False,goal_complete=False))
        raise AssertionError('Actual combined gate failed; retain and repair '+label)
integrated_fixed()
write(RUN/'combined-gates-v1.json',dict(actual_exit_codes=codes,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    exact_two_reviewed_Lean_files_staged_before_harness=True,actual_combined_root_Test_harness_passed=True,
    command_zero_separate_from_inspected_compile_logs=True,source_body_review_passed=True,
    current_site_FINAL_delivery_pending=True,chapter_complete=False,goal_complete=False))
