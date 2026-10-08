from common_reviewed_v2 import *

headers_fixed(1)
assert load(RUN / 'first-leaf-focused-build-v2-exit.json')['exit_code'] == 1
targets = load(CONTRACT / 'targets-v2.json')['rows']
old = PUBLIC.read_text(encoding='utf8')
write(RUN / 'failed-I001-public-v2.lean.raw', PUBLIC.read_bytes())
before = '  rw [integral_finset_sum (Finset.range T)\n    (fun t _ => ((memLp_const u).sub (hL t)).integrable_sq)]'
after = '  rw [integral_finset_sum (Finset.range T)\n    (f := fun t ω => (u - Y t ω)^2)\n    (fun t _ => ((memLp_const u).sub (hL t)).integrable_sq)]'
assert old.count(before) == 1
write(RUN / 'I001-integral-inference-repair-v3.json', dict(actual_failed_build_exit=1,
    failed_public_raw_sha256=sha(RUN / 'failed-I001-public-v2.lean.raw'),
    actual_failed_log_sha256=sha(RUN / 'first-leaf-focused-build-v2.log'),
    typed_obstruction='Lean inferred the finite-integral summand as function subtraction applied after subtraction, and rewrite did not find the intended pointwise square expression.',
    repair='Supply the EXACT pointwise summand through integral_finset_sum named f argument; same integrability certificate and mathematical route.',
    target_header_sha256=targets[0]['header_sha256'], frozen_statement_assumptions_context_unchanged=True,
    no_source_or_terminal_revision=True, package_accepted=False, chapter_complete=False, goal_complete=False))
native('first-worker-failed-v2', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'build', '--status', 'failed',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'IID-I001-V2', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--verifier-evidence', RUN / 'first-leaf-focused-build-v2-exit.json',
    '--progress-class', 'diagnostic', '--obligations-before', '8', '--obligations-after', '8', '--notes',
    'Actual rewrite failure from inferred function-subtraction summand; raw failed public/log retained. Explicit f argument repairs API matching, no mathematical/target weakening.')
PUBLIC.write_bytes(old.replace(before, after).encode('utf8'))
headers_fixed(1)
native('first-worker-running-v3', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'IID-I001-V3', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--notes', 'Same frozen I001, same single route; explicit pointwise summand for finite integral rewrite.')
gate('first-leaf-focused-build-v3', 'lake', 'build', 'BanditRLProof.OnlineGuessingIIDBenchmark')
source = (RUN / 'stabilize-first-leaf-v2.py').read_text(encoding='utf8')
start = "native('first-leaf-fence-v2',"
assert source.count(start) == 1
tail = (start + source.split(start,1)[1]).replace('first-leaf-focused-build-v2-exit.json', 'first-leaf-focused-build-v3-exit.json').replace('IID-I001-V2', 'IID-I001-V3')
exec(compile(tail, str(RUN / 'stabilize-first-leaf-v2.py') + ':body-API-resume-v3', 'exec'))
