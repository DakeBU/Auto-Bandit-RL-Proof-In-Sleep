from publication_guard_v1 import *
import re
fixed();old=load(RUN/'combined-full-harness-v1.json')
out=base64.b64decode(old['stdout_base64']).decode('utf8',errors='replace')
assert old['actual_exit']==1 and 'untracked Lean source under allowlisted tree: BanditRLProof/OnlineProximalComparison.lean' in out
assert 'Build completed successfully (9276 jobs)' in out and 'lake env lean tools/ProofGraphExport.lean' in out
assert 'FAILED (errors=1, skipped=7)' in out and 'Ran 446 tests' in out
source_paths=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix()]
capture('harness-repair-source-stage-v2','git','add',*source_paths)
tracked=set(subprocess.check_output(['git','ls-files','--',*source_paths],encoding='utf8').splitlines());assert tracked==set(source_paths)
write(RUN/'full-harness-failure-classification-v1.json',dict(actual_failed_receipt_sha256=sha(RUN/'combined-full-harness-v1.json'),actual_exit=1,category='Git input inventory gate, not Lean proof failure',detail='Anonymous supplement setUpClass rejects untracked allowlisted new production Lean source. Actual combined root/Tests and exporter succeeded;446tests/errors1/skipped7. No archive publication or anonymous snapshot mutation.',repair='Stage only the two authorized new production/Test sources so git ls-files can see them, then rerun full unchanged harness. No tests/skips/source/statement modification.',actually_staged_paths=source_paths,production_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),chapter_complete=False,whole_Goal_status='ACTIVE'))
event('harness-input-repair-native-v2','repair',dict(scope='Own package input tracking only',failed_receipt_sha256=sha(RUN/'combined-full-harness-v1.json'),classification_sha256=sha(RUN/'full-harness-failure-classification-v1.json'),proof_statement_source_and_test_rules_unchanged=True,chapter_complete=False,goal_complete=False))
fixed()
code,out=capture('combined-full-harness-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','check',required=False)
jobs=list(map(int,re.findall(r'Build completed successfully \((\d+) jobs\)',out)))
tests=re.findall(r'Ran (\d+) tests in ([\d.]+)s',out)
assert code==0 and jobs and tests and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out) and 'check passed' in out
assert 'error: build failed' not in out and 'Lean exited with code 1' not in out and 'forbidden placeholder scan failed' not in out and 'tools/ProofGraphExport.lean' in out
fixed()
write(RUN/'full-harness-inspected-v1.json',dict(actual_exit=code,actual_successful_cached_inclusive_build_jobs=jobs,actual_unittest_runs=[dict(tests=int(n),seconds=float(s)) for n,s in tests],actual_skip_markers=re.findall(r'OK \(skipped=(\d+)\)',out),actual_check_passed=True,actual_ProofGraphExport_compile_present=True,actual_command_receipt_sha256=sha(RUN/'combined-full-harness-v2.json'),prior_actual_failure_retained=sha(RUN/'combined-full-harness-v1.json'),input_tracking_only_repair=sha(RUN/'full-harness-failure-classification-v1.json'),applicable_production_sha256=sha(PUBLIC),applicable_canary_sha256=sha(CANARY),applicable_root_sha256=sha(ROOT/'BanditRLProof.lean'),applicable_Tests_root_sha256=sha(ROOT/'Tests.lean'),fixed_source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},site_registry_pixels_FINAL_native_delivery_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Actual repaired unchanged full harness compiler/unittest/exporter/check markers inspected.')
