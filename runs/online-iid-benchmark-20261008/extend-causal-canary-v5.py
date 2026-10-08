from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN / 'canary-foundation-focused-build-v4-exit.json')['exit_code'] == 0
write(RUN / 'canary-foundation-compiled-v4.lean.raw', CANARY.read_bytes())
body = '''
/-- Initial half, then the most recent strict-past coordinate; only legal inputs are bounded. -/
def lastPolicy (t : ℕ) (z : (↑(Finset.range t) : Type) → ℝ) : ℝ :=
  if h : t = 0 then 1 / 2 else
    z ⟨t - 1, Finset.mem_range.mpr (Nat.sub_lt (Nat.pos_of_ne_zero h) (by omega))⟩

theorem lastPolicy_measurable (t : ℕ) : Measurable (lastPolicy t) := by
  unfold lastPolicy
  split_ifs <;> fun_prop

theorem lastPolicy_legal (t : ℕ) (z : (↑(Finset.range t) : Type) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) : lastPolicy t z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold lastPolicy
  split_ifs
  · norm_num
  · exact hz _

/-- The v1 all-real-inputs policy hypothesis fails, while the reviewed v2 hypothesis holds. -/
theorem lastPolicy_not_globally_bounded :
    ¬ (∀ t z, lastPolicy t z ∈ Set.Icc (0 : ℝ) 1) := by
  intro h
  have bad := h 1 (fun _ => 2)
  norm_num [lastPolicy] at bad

theorem actual_history_independent (t : ℕ) :
    IndepFun (fun ω => lastPolicy t (fun i => observation i ω)) (observation t) iidLaw :=
  history_policy_independent iidLaw observation observation_measurable observation_independent
    t (lastPolicy t) (lastPolicy_measurable t)

theorem actual_history_nonnegative (T : ℕ) :
    0 ≤ expectedFixedRegret iidLaw observation (fun t ω => lastPolicy t (fun i => observation i ω)) T :=
  (history_policy_expectedFixed_excess iidLaw observation observation_measurable observation_sameLaw
    observation_support observation_independent lastPolicy lastPolicy_measurable lastPolicy_legal T).2

theorem actual_history_normalization :
    (∫ ω, ∑ t ∈ Finset.range 2,
      (lastPolicy t (fun i => observation i ω) - observation t ω)^2 ∂iidLaw) / 2 - 1 / 4 =
        expectedFixedRegret iidLaw observation (fun t ω => lastPolicy t (fun i => observation i ω)) 2 / 2 := by
  have h := history_policy_normalized_expectedFixed_excess iidLaw observation observation_measurable
    observation_sameLaw observation_support observation_independent lastPolicy lastPolicy_measurable
    lastPolicy_legal 2 (by norm_num)
  simpa [observation_variance] using h

/-- The fixed benchmark only needs same-law: here every round repeats the identical variable. -/
theorem repeated_target_fixed_minimum (T : ℕ) :
    expectedFixedMinimum iidLaw (fun _ => observation 0) T = (T : ℝ) / 4 := by
  rw [expectedFixedMinimum_eq_variance iidLaw (fun _ => observation 0)
    (fun _ => observation_measurable 0)
    (fun _ => IdentDistrib.refl (observation_measurable 0).aemeasurable)
    (fun _ => observation_support 0), observation_variance]
  ring

theorem infeasible_fixed_comparator_two :
    (∫ ω, ∑ t ∈ Finset.range 2, ((2 : ℝ) - observation t ω)^2 ∂iidLaw) = 5 := by
  rw [expected_fixed_prefix_decomposition iidLaw observation observation_measurable
    observation_sameLaw observation_support, observation_mean, observation_variance]
  norm_num

theorem independent_difference_square :
    (∫ ω, (observation 0 ω - observation 1 ω)^2 ∂iidLaw) = 1 / 2 := by
  have hL (t : ℕ) : MemLp (observation t) 2 iidLaw :=
    memLp_of_bounded (observation_support t) (observation_measurable t).aestronglyMeasurable 2
  have he := independent_prediction_square iidLaw (observation 0) (observation 1) (hL 0) (hL 1)
    (observation_independent.indepFun (by norm_num : (0 : ℕ) ≠ 1))
  have hc := variance_eq_integral (μ := iidLaw) (observation_measurable 0).aemeasurable
  rw [observation_mean] at hc
  simp_rw [observation_mean, observation_variance] at he
  rw [← hc, observation_variance] at he
  norm_num at he
  exact he

/-- Minimum is taken separately on each realized path, unlike expectedFixedMinimum. -/
def hindsightMinimum (ω : ℕ → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - ω t)^2) '' Set.Icc (0 : ℝ) 1)

theorem hindsight_minimum_two : (∫ ω, hindsightMinimum ω 2 ∂iidLaw) = 1 / 4 := by
  have he : ∀ᵐ ω ∂iidLaw,
      hindsightMinimum ω 2 = (observation 0 ω - observation 1 ω)^2 / 2 := by
    filter_upwards [ae_all_iff.2 observation_support] with ω hω
    unfold hindsightMinimum
    rw [squaredLoss_minimum_eq ω 2 (fun t _ => hω t)]
    norm_num [empiricalMean, Finset.sum_range_succ, observation]
    <;> ring
  calc
    (∫ ω, hindsightMinimum ω 2 ∂iidLaw) =
        ∫ ω, (observation 0 ω - observation 1 ω)^2 / 2 ∂iidLaw := integral_congr_ae he
    _ = (∫ ω, (observation 0 ω - observation 1 ω)^2 ∂iidLaw) / 2 := integral_div 2 _
    _ = 1 / 4 := by rw [independent_difference_square]; norm_num

theorem min_and_expectation_do_not_commute :
    (∫ ω, hindsightMinimum ω 2 ∂iidLaw) < expectedFixedMinimum iidLaw observation 2 := by
  rw [hindsight_minimum_two, two_round_fixed_minimum]
  norm_num

/-- This future-aware supplied trace is deliberately NOT a legal causal strategy. -/
theorem current_target_cheating_negative :
    expectedFixedRegret iidLaw observation observation 2 = -1 / 2 := by
  unfold expectedFixedRegret
  rw [two_round_fixed_minimum]
  simp

'''
old = CANARY.read_text(encoding='utf8')
suffix = 'end Tests.OnlineGuessingIIDBenchmark\n'
assert old.endswith(suffix)
CANARY.write_bytes((old[:-len(suffix)] + body + suffix).encode('utf8'))
write(RUN / 'causal-canary-candidate-v5.lean.raw', CANARY.read_bytes())
gate('causal-canary-focused-build-v5', 'lake', 'build', 'Tests.OnlineGuessingIIDBenchmarkCanary')
headers_fixed(8)
