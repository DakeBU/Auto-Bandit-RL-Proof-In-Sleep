from common_integrated_v1 import *

fixed_integrated()
gate('contributor-committed-exact-base-v2', sys.executable, '-B', '-X', 'utf8', 'tools/check_contributor_contract.py', '--base', BASE)
log = (RUN / 'contributor-committed-exact-base-v2.log').read_text(encoding='utf8')
assert 'affected production paths: 5' in log and 'changed contribution contracts: 1' in log, log
assert 'CONTRIBUTOR CONTRACT PASSED' in log or 'contributor contract passed' in log.lower(), log
write(RUN / 'integrated-gates-v2.json', dict(status='Actual combined root/Tests/full harness/own shadow and nonvacuous committed exact-base contributor passed',
    source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    root_log_sha256=sha(RUN / 'combined-root-v1.log'), Tests_log_sha256=sha(RUN / 'combined-Tests-v1.log'),
    harness_log_sha256=sha(RUN / 'full-harness-v1.log'), public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    affected_production_paths=5, changed_contracts=1, committed_contributor_receipt_sha256=sha(RUN / 'contributor-committed-exact-base-v2-exit.json'),
    initial_zero_path_contributor_superseded_as_vacuous=True, inherited_main_five_modules_unwaived=True,
    root_jobs=9096, Tests_jobs=9251, harness_tests=472, harness_skips=7,
    globalSGB_unchanged=True, clean_site_FINAL_native_PR_pending=True, chapter_complete=False, goal_complete=False))
fixed_integrated()
print('Actual committed contributor gate: five production paths/one contract; original N/A superseded, all chapter/program obligations remain.')
