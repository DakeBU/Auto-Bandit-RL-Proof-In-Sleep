from common_v1 import *
fixed(integrated=True)
fail=load(RUN/'full-harness-v1-exit.json');assert fail['exit_code']==1
text=(RUN/'full-harness-v1.log').read_text(encoding='utf-8')
assert 'untracked Lean source under allowlisted tree: Tests/OnlineLearningRegretDomainsCanary.lean' in text and 'Ran 446 tests' in text
write(RUN/'integrated-repair-v2.json',dict(stage='repair',failure_log_sha256=sha(RUN/'full-harness-v1.log'),actual_reason='Anonymous supplement test refuses untracked allowlisted Lean source; new approved canary was not yet indexed',failed_python_tests=446,existing_skips=7,root_and_Tests_passed=True,mathematical_target_changed=False,proof_bytes_changed=False,remedy='Stage only new owned canary, then rerun complete harness; no frozen anonymous snapshot or packaging implementation change',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('integrated-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,repair_record=(RUN/'integrated-repair-v2.json').as_posix(),contract_version=1,mathematical_target_changed=False,chapter_complete=False,goal_complete=False)))
gate('index-owned-canary-v2','git','add','--',CANARY)
gate('full-harness-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
gate('contributor-exact-base-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
label='contributor-origin-main-diagnostic-v2';log=RUN/(label+'.log');assert not log.exists();start=time.time()
with log.open('wb') as stream:child=subprocess.run([sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'],stdout=stream,stderr=subprocess.STDOUT)
write(RUN/(label+'-exit.json'),dict(command='tools/check_contributor_contract.py --base origin/main',cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log),purpose='Actual whole-stack main-relative diagnostic; unrelated mandatory gaps unwaived'))
write(RUN/'integrated-gates-v2.json',dict(status='Actual root/Tests/fullharness-v2/exact PR189 base contributor passed after indexing repair',root_log_sha256=sha(RUN/'combined-root-v1.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v1.log'),harness_log_sha256=sha(RUN/'full-harness-v2.log'),contributor_log_sha256=sha(RUN/'contributor-exact-base-v2.log'),main_diagnostic_exit_code=child.returncode,existing_math_exact=True,new_production_math=0,canary_sha256=sha(CANARY),public_documentation_sha256=sha(PUBLIC),site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
native('integrated-repair-candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,repair_record=(RUN/'integrated-repair-v2.json').as_posix(),integrated_gates=(RUN/'integrated-gates-v2.json').as_posix(),mathematical_target_changed=False,chapter_complete=False,goal_complete=False)))
fixed(integrated=True);print('Actual integrated repair complete; main diagnostic exit',child.returncode,'; site/FINAL pending.')
