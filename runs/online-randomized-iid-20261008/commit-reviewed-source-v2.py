from common_integrated_v2 import *
from commit_owned_v2 import stage_owned, commit_owned

fixed_integrated()
assert load(RUN/'combined-gates-v3.json')['status'].startswith('Actual combined')
failed=load(RUN/'source-full-diff-v2-exit.json')
assert failed['actual_exit_code']==2 and not failed['unexcluded_passed']
expected={RUN.relative_to(ROOT).as_posix()+'/'+n for n in ['combined-root-v2.log','combined-Tests-v2.log',
    'full-harness-v2.log','full-harness-v3.log']}
assert {r['path'] for r in failed['findings']}==expected
exceptions=[]
for p in sorted(expected|{(RUN/'source-full-diff-v2.log').relative_to(ROOT).as_posix()}):
    exceptions.append(dict(path=p,sha256=sha(p),
        reason='Preserve exact actual Lean/harness stdout or the actual failed whitespace-check stdout quoting it; no production/source/Test/reader/contract/helper exemption.'))
write(RUN/'diff-raw-bound-exceptions-v2.json',dict(exceptions=exceptions,
    scope='Five exact SHA-bound raw verification/failure stdout files ONLY. Zero source/Test/reader/contract/executable-helper exemptions.',
    unexcluded_diff_check_exit=2,FINAL_raw_exception_judgment_pending=True,chapter_complete=False,goal_complete=False))
gate('source-scope-pre-commit-v2',sys.executable,'-B','-X','utf8',RUN/'audit-owned-scope-v2.py','pre-commit-v2')
stage_owned()
gate('source-scoped-diff-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','source-v2')
# Every writer has returned before final raw staging/commit, avoiding partial evidence bytes.
commit_owned('Derive causal IID square-loss excess with independent private randomness')
fixed_integrated()
print('Actual clean own source commit:',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip())
