from common_reviewed_v2 import *

headers_fixed(2)
targets = load(CONTRACT / 'targets-v2.json')['rows']
assert load(RUN / 'I002-focused-build-v2-exit.json')['exit_code'] == 1
write(RUN / 'failed-I002-public-v2.lean.raw', PUBLIC.read_bytes())
write(RUN / 'I002-beta-repair-v3.json', dict(
    obstruction='Rewriting does not beta-reduce the image function application in IsLeast membership and lower-bound goals.',
    repair='Expose the identical pointwise integral with change before the same decomposition rewrite.',
    frozen_header_sha256=targets[1]['header_sha256'], source_terminal_context_unchanged=True,
    package_accepted=False, chapter_complete=False, goal_complete=False))
native('I002-worker-failed-v2', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'build', '--status', 'failed',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'IID-I002-V2', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--verifier-evidence', RUN / 'I002-focused-build-v2-exit.json',
    '--progress-class', 'diagnostic', '--obligations-before', '7', '--obligations-after', '7',
    '--notes', 'Actual IsLeast rewrite beta-redex obstruction; raw failure preserved. No mathematical or header revision.')
old = PUBLIC.read_text(encoding='utf8')
before = '    rw [expected_fixed_prefix_decomposition μ Y hY hlaw hb T]'
assert old.count(before) == 2
first = '    change (∫ ω, ((∫ ω, Y 0 ω ∂μ) - Y t ω)^2 ∂μ)'  # Not used: finite sum is retained below.
old = old.replace('    rw [expected_fixed_prefix_decomposition μ Y hY hlaw hb T]\n    simp',
    '    change (∫ ω, ∑ t ∈ Finset.range T, ((∫ ω, Y 0 ω ∂μ) - Y t ω)^2 ∂μ) = _\n    rw [expected_fixed_prefix_decomposition μ Y hY hlaw hb T]\n    simp')
old = old.replace('  · rintro z ⟨u, _, rfl⟩\n    rw',
    '  · rintro z ⟨u, _, rfl⟩\n    change _ ≤ (∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ)\n    rw')
PUBLIC.write_bytes(old.encode('utf8'))
headers_fixed(2)
native('I002-worker-running-v3', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'IID-I002-V3', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--notes', 'Same frozen IsLeast producer; expose beta-reduced integral goals.')
gate('I002-focused-build-v3', 'lake', 'build', 'BanditRLProof.OnlineGuessingIIDBenchmark')
source = (RUN / 'prove-minimum-I002-I003-v2.py').read_text(encoding='utf8')
tail = source[source.index("    native(row['id'] + '-fence-v2'"):source.index("print('Actual I001")]
row, index, attempt, label = targets[1], 1, 'IID-I002-V3', 'I002-focused-build-v3'
exec(compile('\n'.join(line[4:] for line in tail.splitlines()), 'I002-v2-evidence-resumed-v3', 'exec'))
# Resume only the dependency-ready I003 iteration in the original exact script.
remaining = source[source.index('for index, body in zip([1,2], bodies):'):]
remaining = remaining.replace('zip([1,2], bodies)', 'zip([2], bodies[1:])')
bodies = [None, ' := by\n  unfold expectedFixedMinimum\n  exact (expected_fixed_prefix_minimum μ Y hY hlaw hb T).2.csInf_eq\n\n']
exec(compile(remaining, 'I003-original-v2-resume', 'exec'))
