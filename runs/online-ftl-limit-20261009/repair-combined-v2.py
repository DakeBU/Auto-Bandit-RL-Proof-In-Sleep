from common_body_v1 import *

integrated_fixed()
failure = load(RUN / 'combined-gates-failure-v1.json')
assert failure['actual_exit_codes'] == [0, 0, 1]
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], encoding='utf8').strip()
lean_paths = [PUBLIC.relative_to(ROOT).as_posix(), CANARY.relative_to(ROOT).as_posix()]
write(RUN / 'combined-repair-v2.json', dict(
    original_failure='combined-full-harness-v1.log', original_actual_exit=1,
    cause='AnonymousSupplementTests.setUpClass rejects new untracked allowlisted Lean sources.',
    repair='Stage only the two reviewed Lean files before rerunning the full harness.',
    staged_paths=lean_paths, public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    no_source_statement_proof_toolchain_or_harness_change=True,
    original_failure_retained=True, package_accepted=False, goal_complete=False))
gate('combined-stage-repair-v2', 'git', 'add', *lean_paths)
integrated_fixed()
code = gate('combined-full-harness-v2', sys.executable, '-B', '-X', 'utf8',
            'tools/bandit.py', 'check', required=False)
if code:
    write(RUN / 'combined-gates-failure-v2.json', dict(actual_exit_codes=[0, 0, code],
        failed='combined-full-harness-v2', original_failure_retained=True,
        public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY), package_accepted=False))
    raise AssertionError('Actual repaired harness failed; inspect retained v2 log')
integrated_fixed()
commands = ['combined-root-v1', 'combined-Tests-v1', 'combined-full-harness-v2']
for name in commands:
    receipt = load(RUN / (name + '-exit.json'))
    assert receipt['actual_exit'] == 0 and receipt['log_sha256'] == sha(RUN / (name + '.log'))
write(RUN / 'combined-gates-v1.json', dict(actual_exit_codes=[0, 0, 0],
    actual_receipts=[name + '-exit.json' for name in commands],
    original_failure='combined-gates-failure-v1.json', repair='combined-repair-v2.json',
    public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    actual_combined_root_Test_harness_passed=True,
    command_zero_separate_from_inspected_compile_logs=True,
    source_body_review_passed=True, current_site_FINAL_delivery_pending=True,
    chapter_complete=False, goal_complete=False))
print('Actual root-v1/Tests-v1/harness-v2 passed; original harness failure retained.', flush=True)
