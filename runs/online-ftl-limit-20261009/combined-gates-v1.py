from common_body_v1 import *
integrated_fixed()
codes=[]
for label,args in [('combined-root-v1',['lake','build','BanditRLProof']),
    ('combined-Tests-v1',['lake','build','Tests']),
    ('combined-full-harness-v1',[sys.executable,'-B','-X','utf8','tools/bandit.py','check'])]:
    code=gate(label,*args,required=False)
    codes.append(code)
    if code:
        write(RUN/'combined-gates-failure-v1.json',dict(actual_exit_codes=codes,failed=label,
            public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),package_accepted=False,goal_complete=False))
        raise AssertionError('Actual combined gate failed; repair retained '+label)
integrated_fixed()
write(RUN/'combined-gates-v1.json',dict(actual_exit_codes=codes,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    actual_combined_root_Test_harness_passed=True,command_zero_separate_from_inspected_compile_logs=True,
    source_body_review_passed=True,current_site_FINAL_delivery_pending=True,chapter_complete=False,goal_complete=False))
print('Actual combinedroot/Tests/fullharness0; applicable new Lean gate, current site/FINAL pending.',flush=True)
