from common_integrated_v2 import *
from commit_owned_v2 import stage_owned, commit_owned

fixed_integrated()
assert load(RUN/'contributor-committed-exact-base-v2-exit.json')['exit_code']==0
log=(RUN/'contributor-committed-exact-base-v2.log').read_text(encoding='utf8')
assert 'affected production paths: 5' in log and 'changed contribution contracts: 1' in log
assert 'Contributor contract passed.' in log and 'changed paths: 662' in log
write(RUN/'contributor-output-parser-failure-repair-v3.json',dict(
    actual_native_gate_exit=0,failed_helper='contributor-gate-and-clean-evidence-v2.py',
    incorrect_helper_assertion='Guessed one prose sentence instead of reading the actual separate CLI count labels.',
    repair='Bind exact actual affected-production-paths5 and contribution-contracts1 CLI labels and authoritative native exit0; retain original helper/log.',
    mathematical_source_changed=False,gate_waived=False,package_accepted=False,chapter_complete=False,goal_complete=False))
source_head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert source_head=='0b077dd5b5b7c3f9e254baed756ab427612e6b00' or source_head.startswith('0b077dd5')
write(RUN/'integrated-gates-v2.json',dict(actual_source_commit=source_head,exact_stacked_base=BASE,
    affected_production_paths=5,own_contribution_contracts=1,actual_changed_paths_at_gate=662,
    actual_nonzero_committed_diff=True,contributor_gate='contributor-committed-exact-base-v2-exit.json',
    actual_native_output_checked=True,preserved_helper_output_parser_failure='contributor-output-parser-failure-repair-v3.json',
    root_jobs=9098,Tests_jobs=9255,actual_harness_tests=472,actual_harness_skips=7,
    combined_gates='combined-gates-v3.json',preserved_tracking_failure='full-harness-v2-exit.json',
    full_unexcluded_whitespace_exit=2,exact_raw_stdout_exceptions=5,executable_helper_exemptions=0,
    inherited_main_relative_five_source_audits='REQUIRED unwaived',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    current_site_pixels_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
stage_owned()
gate('validation-evidence-scoped-diff-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','validation-v3')
commit_owned('Record complete combined gates and exact-base contribution audit')
fixed_integrated()
print('Actual clean validation-evidence commit:',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip())
