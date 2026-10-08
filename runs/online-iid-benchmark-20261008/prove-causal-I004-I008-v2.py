from common_reviewed_v2 import *

headers_fixed(3)
assert load(RUN / 'I003-focused-build-v2-exit.json')['exit_code'] == 0
write(RUN / 'I001-I003-compiled-public-v3.lean.raw', PUBLIC.read_bytes())
targets = load(CONTRACT / 'targets-v2.json')['rows']
bodies = [
''' := by
  have hL (t : ℕ) : MemLp (Y t) 2 μ :=
    memLp_of_bounded (hb t) (hY t).aestronglyMeasurable 2
  rw [integral_finset_sum (Finset.range T)
    (f := fun t ω => (prediction t ω - Y t ω)^2)
    (fun t _ => ((hP t).sub (hL t)).integrable_sq)]
  have heq (t : ℕ) :
      (∫ ω, (prediction t ω - Y t ω)^2 ∂μ) =
        (∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) + variance (Y 0) μ := by
    simpa only [(hlaw t).integral_eq, (hlaw t).variance_eq] using
      independent_prediction_square μ (prediction t) (Y t) (hP t) (hL t) (hInd t)
  simp_rw [heq]
  simp [Finset.sum_add_distrib]

''',
''' := by
  have hall : ∀ᵐ ω ∂μ, ∀ t, Y t ω ∈ Set.Icc (0 : ℝ) 1 := ae_all_iff.2 hb
  have hP (t : ℕ) : MemLp (fun ω => policy t (fun i => Y i ω)) 2 μ := by
    apply memLp_of_bounded (a := 0) (b := 1) _
      ((hp t).comp (measurable_pi_lambda _ (fun i => hY i))).aestronglyMeasurable
    filter_upwards [hall] with ω hω
    exact hpb t _ (fun i => hω i)
  have hInd (t : ℕ) : IndepFun (fun ω => policy t (fun i => Y i ω)) (Y t) μ :=
    history_policy_independent μ Y hY hind t (policy t) (hp t)
  have he : expectedFixedRegret μ Y (fun t ω => policy t (fun i => Y i ω)) T =
      ∑ t ∈ Finset.range T, ∫ ω, (policy t (fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
    unfold expectedFixedRegret
    rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
    exact iid_cumulative_prediction_decomposition μ Y hY hlaw hb _ hP hInd T
  refine ⟨he, ?_⟩
  rw [he]
  exact Finset.sum_nonneg (fun t _ => integral_nonneg (fun ω => sq_nonneg _))

''',
''' := by
  have hall : ∀ᵐ ω ∂μ, ∀ t, Y t ω ∈ Set.Icc (0 : ℝ) 1 := ae_all_iff.2 hb
  have hP (t : ℕ) : MemLp (fun ω => meanPredict (fun i => Y i ω) t) 2 μ := by
    apply memLp_of_bounded (a := 0) (b := 1) _
      (meanPredict_measurable Y hY t).aestronglyMeasurable
    filter_upwards [hall] with ω hω
    exact meanPredict_mem (fun i => Y i ω) t (fun i _ => hω i)
  have hInd (t : ℕ) : IndepFun (fun ω => meanPredict (fun i => Y i ω) t) (Y t) μ :=
    meanPredict_independent μ Y hY hind t
  have he : expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T =
      ∑ t ∈ Finset.range T,
        ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
    unfold expectedFixedRegret
    rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
    exact iid_cumulative_prediction_decomposition μ Y hY hlaw hb _ hP hInd T
  refine ⟨he, ?_⟩
  rw [he]
  exact Finset.sum_nonneg (fun t _ => integral_nonneg (fun ω => sq_nonneg _))

''',
''' := by
  refine ⟨(expected_fixed_prefix_minimum μ Y hY hlaw hb T).1, ?_⟩
  unfold expectedFixedRegret
  rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T,
    expected_fixed_prefix_decomposition μ Y hY hlaw hb T]
  simp

''',
''' := by
  unfold expectedFixedRegret
  rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
  exact normalized_excess _ _ T hT

''']
comments = [
    'Independent-prediction consumer; actual strict-past producers follow.',
    'Legal-input measurable history policy: a.s. feasibility and independence are derived.',
    'Actual first-half strict-past meanPredict: a.s. support produces L2 without pointwise strengthening.',
    'The distribution-known mean attains the expected fixed benchmark; not an unknown-law learner.',
    'Positive-horizon finite normalization; no asymptotic convergence is asserted.'
]
for index, body, comment in zip(range(3,8), bodies, comments):
    row = targets[index]
    attempt = 'IID-' + row['id'] + '-V2'
    native(row['id'] + '-worker-running-v2', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running',
        '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', attempt, '--harness', 'hierarchical',
        '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--new-declaration', row['name'],
        '--notes', comment + ' Exact dependency-ready frozen leaf; single lower route, no target edit.')
    old = PUBLIC.read_text(encoding='utf8')
    suffix = 'end BanditRL.OnlineLearning\n'
    assert old.endswith(suffix)
    PUBLIC.write_bytes((old[:-len(suffix)] + '/-- ' + comment + ' -/\n' + row['header'] + body + suffix).encode('utf8'))
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
        comment + ' Actual frozen body builds. Only this eight-target frontier advances; BODY/canary/kernel/combined/reader/FINAL gates pending.')
    write(RUN / ('30_worker-' + row['id'] + '-v2.md'), comment + '\nActual focused build, frozen header and native trial separately recorded. Package/chapter/Goal not accepted.')
    write(RUN / ('leaf-progress-' + row['id'] + '-v2.json'), dict(contract_version=2, contract_targets=8,
        closed=[r['name'] for r in targets[:index+1]], remaining=[r['name'] for r in targets[index+1:]],
        public_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
print('Eight exact actual bodies compile; required candidate/acceptance gates remain.')
