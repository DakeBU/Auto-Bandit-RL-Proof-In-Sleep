from common_reviewed_v2 import *

headers_fixed(1)
targets = load(CONTRACT / 'targets-v2.json')['rows']
assert load(RUN / 'first-leaf-focused-build-v3-exit.json')['exit_code'] == 0
write(RUN / 'I001-compiled-public-v3.lean.raw', PUBLIC.read_bytes())
bodies = [
''' := by
  have hI : Integrable (Y 0) μ :=
    (memLp_of_bounded (hb 0) (hY 0).aestronglyMeasurable 2).integrable (by norm_num)
  have hm0 : 0 ≤ ∫ ω, Y 0 ω ∂μ :=
    integral_nonneg_of_ae ((hb 0).mono (fun _ h => h.1))
  have hm1 : (∫ ω, Y 0 ω ∂μ) ≤ 1 := by
    have h := integral_mono_ae hI (integrable_const (1 : ℝ))
      ((hb 0).mono (fun _ h => h.2))
    simpa using h
  have hm : (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hm0, hm1⟩
  refine ⟨hm, ⟨?_, ?_⟩⟩
  · refine ⟨∫ ω, Y 0 ω ∂μ, hm, ?_⟩
    rw [expected_fixed_prefix_decomposition μ Y hY hlaw hb T]
    simp
  · rintro z ⟨u, _, rfl⟩
    rw [expected_fixed_prefix_decomposition μ Y hY hlaw hb T]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg T) (sq_nonneg _))

''',
''' := by
  unfold expectedFixedMinimum
  exact (expected_fixed_prefix_minimum μ Y hY hlaw hb T).2.csInf_eq

''']
for index, body in zip([1,2], bodies):
    row = targets[index]
    attempt = 'IID-' + row['id'] + '-V2'
    native(row['id'] + '-worker-running-v2', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running',
        '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', attempt, '--harness', 'hierarchical',
        '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--new-declaration', row['name'],
        '--notes', 'Dependency-ready exact minimum leaf; derive actual mean feasibility/image membership/lower comparisons before applying csInf_eq. No supplied argmin or target edit.')
    old = PUBLIC.read_text(encoding='utf8')
    suffix = 'end BanditRL.OnlineLearning\n'
    assert old.endswith(suffix)
    PUBLIC.write_bytes((old[:-len(suffix)] + '/-- Produced expected-fixed minimum; zero horizon has no uniqueness claim. -/\n' +
        row['header'] + body + suffix).encode('utf8'))
    headers_fixed(index+1)
    label = row['id'] + '-focused-build-v2'
    gate(label, 'lake', 'build', 'BanditRLProof.OnlineGuessingIIDBenchmark')
    native(row['id'] + '-fence-v2', 'statement-fence', '--declaration', row['name'], '--file', PUBLIC,
        '--output', RUN / (row['id'] + '-fence-v2.json'))
    native(row['id'] + '-safe-verify-v2', 'safe-verify', '--fence', RUN / (row['id'] + '-fence-v2.json'), '--lean-file', PUBLIC)
    native(row['id'] + '-worker-compiled-v2', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'build', '--status', 'compiled',
        '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', attempt, '--harness', 'hierarchical',
        '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--new-declaration', row['name'],
        '--verifier-evidence', RUN / (label + '-exit.json'), '--progress-class', 'compiled-leaf',
        '--obligations-before', str(8-index), '--obligations-after', str(7-index), '--notes',
        'Actual frozen body focused-builds. IsLeast is produced by actual feasible population mean plus all lower comparisons; infimum adapter uses that certificate. Only eight-target frontier advances, package/reader/canary/combined/FINAL gates pending.')
    write(RUN / ('30_worker-' + row['id'] + '-v2.md'),
        'Actual exact frozen ' + row['id'] + ' body compiles; actual a.s. population-mean feasibility and nonempty attained real loss image precede infimum identity. '
        'Source fixed comparator stays outside expectation; no hindsight interchange, no uniqueness atT0. Body/build/fence/trial separate, no package/chapter/Goal acceptance.')
    write(RUN / ('leaf-progress-' + row['id'] + '-v2.json'), dict(contract_version=2, contract_targets=8,
        closed=[r['name'] for r in targets[:index+1]], remaining=[r['name'] for r in targets[index+1:]],
        public_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
    headers_fixed(index+1)
print('Actual I001–I003 compiled; fixed expected minimum produced. Five exact targets remain, package not accepted.')
