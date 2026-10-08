import BanditRLProof.OnlineGuessingIIDBenchmark
import BanditRLProof.OnlineSquareMinimum
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
open MeasureTheory ProbabilityTheory BanditRL.OnlineLearning
open scoped ENNReal
namespace Tests.OnlineGuessingIIDBenchmark

/-- Real-valued coordinates include illegal off-support paths; support is only a.s. -/
def coinLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

instance coinLaw_probability : IsProbabilityMeasure coinLaw := by
  constructor
  norm_num [coinLaw, ENNReal.inv_two_add_inv_two]

def iidLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => coinLaw)

instance iidLaw_probability : IsProbabilityMeasure iidLaw := by
  unfold iidLaw
  infer_instance

def observation (t : ℕ) (ω : ℕ → ℝ) : ℝ := ω t

theorem coinLaw_support : ∀ᵐ x ∂coinLaw, x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [coinLaw, ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure <;> simp

theorem coinLaw_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂coinLaw) = (f 0 + f 1) / 2 := by
  have h0 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h1 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  rw [coinLaw, integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure]
  simp only [integral_dirac]
  norm_num
  ring

theorem observation_measurable (t : ℕ) : Measurable (observation t) := measurable_pi_apply t

theorem observation_has_coinLaw (t : ℕ) :
    IdentDistrib (observation t) (fun x : ℝ => x) iidLaw coinLaw := by
  refine ⟨(observation_measurable t).aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa [iidLaw, observation] using Measure.infinitePi_map_eval (fun _ : ℕ => coinLaw) t

theorem observation_sameLaw (t : ℕ) :
    IdentDistrib (observation t) (observation 0) iidLaw iidLaw :=
  (observation_has_coinLaw t).trans (observation_has_coinLaw 0).symm

theorem observation_support (t : ℕ) :
    ∀ᵐ ω ∂iidLaw, observation t ω ∈ Set.Icc (0 : ℝ) 1 :=
  (observation_has_coinLaw t).symm.ae_mem_snd measurableSet_Icc coinLaw_support

theorem observation_independent : iIndepFun observation iidLaw := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ => coinLaw)
    (X := fun _ : ℕ => fun x : ℝ => x) (fun _ => measurable_id)

theorem observation_mean (t : ℕ) : (∫ ω, observation t ω ∂iidLaw) = 1 / 2 := by
  rw [(observation_has_coinLaw t).integral_eq, coinLaw_integral]
  norm_num

theorem observation_variance (t : ℕ) : variance (observation t) iidLaw = 1 / 4 := by
  rw [(observation_has_coinLaw t).variance_eq,
    variance_eq_integral (X := fun x : ℝ => x) (μ := coinLaw) measurable_id.aemeasurable, coinLaw_integral, coinLaw_integral]
  norm_num

/-- A concrete off-support path disproves the old pointwise-support hypothesis. -/
theorem support_is_not_pointwise :
    ¬ (∀ t ω, observation t ω ∈ Set.Icc (0 : ℝ) 1) := by
  intro h
  have bad := h 0 (fun _ => 2)
  norm_num [observation] at bad

theorem empty_minimum : expectedFixedMinimum iidLaw observation 0 = 0 := by
  rw [expectedFixedMinimum_eq_variance iidLaw observation observation_measurable
    observation_sameLaw observation_support]
  simp

theorem two_round_fixed_minimum : expectedFixedMinimum iidLaw observation 2 = 1 / 2 := by
  rw [expectedFixedMinimum_eq_variance iidLaw observation observation_measurable
    observation_sameLaw observation_support, observation_variance]
  norm_num

theorem actual_mean_attainment :
    IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range 2, (u - observation t ω)^2 ∂iidLaw) ''
      Set.Icc (0 : ℝ) 1) (1 / 2) := by
  have h := (expected_fixed_prefix_minimum iidLaw observation observation_measurable
    observation_sameLaw observation_support 2).2
  norm_num [observation_variance] at h
  exact h

theorem actual_meanPredict_nonnegative (T : ℕ) :
    0 ≤ expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T := by
  exact (meanPredict_expectedFixed_excess iidLaw observation observation_measurable
    observation_sameLaw observation_support observation_independent T).2

theorem meanPredict_two_round_excess :
    expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = 1 / 4 := by
  have he := (meanPredict_expectedFixed_excess iidLaw observation observation_measurable
    observation_sameLaw observation_support observation_independent 2).1
  have hcenter : (∫ ω, (observation 0 ω - 1 / 2)^2 ∂iidLaw) = 1 / 4 := by
    have hv := variance_eq_integral (μ := iidLaw) (observation_measurable 0).aemeasurable
    rw [observation_mean] at hv
    exact hv.symm.trans (observation_variance 0)
  simp_rw [observation_mean] at he
  simp [Finset.sum_range_succ, meanPredict, empiricalMean, observation] at he
  simpa [meanPredict, empiricalMean] using he.trans (by simpa [observation] using hcenter)

theorem constant_known_mean_zero (T : ℕ) :
    expectedFixedRegret iidLaw observation (fun _ _ => (1 / 2 : ℝ)) T = 0 := by
  have he := (constant_mean_expectedFixed_excess_zero iidLaw observation observation_measurable
    observation_sameLaw observation_support T).2
  simpa [observation_mean] using he


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
  norm_num

end Tests.OnlineGuessingIIDBenchmark
