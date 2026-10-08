from common_integrated_v2 import *
from commit_owned_v2 import stage_owned, commit_owned

fixed_integrated()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
source_head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
gate('contributor-committed-exact-base-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
log=(RUN/'contributor-committed-exact-base-v2.log').read_text(encoding='utf8')
assert '5 production paths covered by 1 contribution contract' in log,log
write(RUN/'integrated-gates-v2.json',dict(actual_source_commit=source_head,exact_stacked_base=BASE,
    affected_production_paths=5,own_contribution_contracts=1,
    actual_nonzero_committed_diff=True,contributor_gate='contributor-committed-exact-base-v2-exit.json',
    root_jobs=9098,Tests_jobs=9255,actual_harness_tests=472,actual_harness_skips=7,
    combined_gates='combined-gates-v3.json',preserved_tracking_failure='full-harness-v2-exit.json',
    full_unexcluded_whitespace_exit=2,exact_raw_stdout_exceptions=5,executable_helper_exemptions=0,
    inherited_main_relative_five_source_audits='REQUIRED unwaived',
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    current_site_pixels_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
stage_owned()
gate('validation-evidence-scoped-diff-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','validation-v2')
commit_owned('Record complete combined gates and exact-base contribution audit')
fixed_integrated()
print('Actual clean validation-evidence commit:',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip())
