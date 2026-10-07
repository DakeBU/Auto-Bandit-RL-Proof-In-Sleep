from common_v1 import *
fixed(True);assert load(RUN/'full-harness-v1-exit.json')['exit_code']==1
raw=(RUN/'full-harness-v1.log').read_text(encoding='utf-8')
assert 'untracked Lean source under allowlisted tree: Tests/OnlineLearningFoundationsCanary.lean' in raw
write(RUN/'harness-tracking-repair-v2.json',dict(failed_log_sha256=sha(RUN/'full-harness-v1.log'),failed_exit_sha256=sha(RUN/'full-harness-v1-exit.json'),cause='New Lean test module is not yet Git-tracked; the existing anonymous-supplement fixture fails closed on untracked allowlisted Lean source.',observed_first_run_tests=440,observed_skips=7,observed_errors=1,repair='Scoped candidate commit of BODY-reviewed proof/tests/reader and evidence before rerunning full gate; do not weaken source-tree checker or modify anonymous frozen artifacts.',source_statement_or_proof_target_change=False,original_failure_retained=True,candidate_commit_is_not_acceptance=True,full_gate='pending actual v2'))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Track reviewed Be-the-Leader candidate before full source-tree gate'],check=True)
gate('full-harness-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
jobs={}
for label in ['combined-root-v1','combined-Tests-v1']:
 assert load(RUN/(label+'-exit.json'))['exit_code']==0
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
raw=(RUN/'full-harness-v2.log').read_text(encoding='utf-8');tests=re.search(r'Ran (\d+) tests?',raw);skips=re.search(r'OK \(skipped=(\d+)\)',raw)
assert tests and 'check passed' in raw and 'FAILED (' not in raw
write(RUN/'combined-gates-v1.json',dict(status='actual-root-Tests-full-harness-passed',jobs_including_cached=jobs,full_tests=int(tests.group(1)),existing_skips=int(skips.group(1)) if skips else 0,successful_full_harness='full-harness-v2',failed_untracked_source_gate_retained=True,current_reader_and_seven_new_tests_included=True,candidate_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),new_public_math=0,new_named_validation_proofs=7,new_source_math_closures=0,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Actual combined gates PASS after tracked-source repair:',jobs,'tests',tests.group(1),'skips',skips.group(1) if skips else 0)
