from common_integrated_v2 import *

fixed_integrated()
assert load(RUN/'full-harness-v2-exit.json')['exit_code']==1
assert 'untracked Lean source under allowlisted tree: BanditRLProof/OnlineGuessingRandomizedIID.lean' in (RUN/'full-harness-v2.log').read_text(encoding='utf8')
for label in ['combined-root-v2','combined-Tests-v2','candidate-frontier-shadow-v2']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
write(RUN/'full-harness-failure-repair-v3.json',dict(actual_failed_gate='full-harness-v2-exit.json',
    actual_failed_tests=446,actual_failed_skips=7,
    failure='AnonymousSupplementTests refuses newly created untracked Lean source in allowlisted source trees.',
    repair='Stage exactly the two owned compiled public/Test modules so the existing allowlisted source audit can inspect them; no test/export/anonymous snapshot waiver or modification.',
    changed_mathematical_source=False,modified_test_infrastructure=False,full_gate_still_required=True))
child=subprocess.run(['git','-c','core.autocrlf=false','add','--',PUBLIC.as_posix(),CANARY.as_posix()],
    stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
for p in [PUBLIC,CANARY]: assert subprocess.check_output(['git','show',':'+p.as_posix()])==p.read_bytes()
fixed_integrated()
native('full-harness-v3','check')
write(RUN/'combined-gates-v3.json',dict(status='Actual combined root/Tests/full harness/own scoped shadow passed.',
    root_receipt='combined-root-v2-exit.json',Tests_receipt='combined-Tests-v2-exit.json',
    actual_harness_receipt='full-harness-v3-exit.json',preserved_failed_harness_receipt='full-harness-v2-exit.json',
    root_log_sha256=sha(RUN/'combined-root-v2.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v2.log'),
    harness_log_sha256=sha(RUN/'full-harness-v3.log'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    contributor='Actual committed exact-base production diff gate REQUIRED; no zero-path acceptance.',
    globalSGB_unchanged=True,site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed_integrated()
print('Actual complete combined gate passed after tracking-only repair; all original failures retained.')
