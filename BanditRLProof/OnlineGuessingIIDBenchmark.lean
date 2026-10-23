import BanditRLProof.OnlineLearningHistory
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory ProbabilityTheory

namespace BanditRL.OnlineLearning

noncomputable def expectedFixedMinimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def expectedFixedRegret {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    expectedFixedMinimum μ Y T

/-- Same-law expected fixed loss; a.s. support produces L2 before finite integration. -/
theorem expected_fixed_prefix_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (u : ℝ) :
    (∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) =
      (T : ℝ) * variance (Y 0) μ +
        (T : ℝ) * (u - ∫ ω, Y 0 ω ∂μ)^2 := by
  have hL (t : ℕ) : MemLp (Y t) 2 μ :=
    memLp_of_bounded (hb t) (hY t).aestronglyMeasurable 2
  rw [integral_finset_sum (Finset.range T)
    (f := fun t ω => (u - Y t ω)^2)
    (fun t _ => ((memLp_const u).sub (hL t)).integrable_sq)]
  have heq (t : ℕ) :
      (∫ ω, (u - Y t ω)^2 ∂μ) =
        variance (Y 0) μ + (u - ∫ ω, Y 0 ω ∂μ)^2 := by
    simpa only [(hlaw t).integral_eq, (hlaw t).variance_eq] using
      expected_square_decomposition μ (Y t) (hL t) u
  simp_rw [heq]
  simp [Finset.sum_add_distrib]

/-- Produced expected-fixed minimum; zero horizon has no uniqueness claim. -/
theorem expected_fixed_prefix_minimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
        Set.Icc (0 : ℝ) 1) ((T : ℝ) * variance (Y 0) μ) := by
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
    change (∫ ω, ∑ t ∈ Finset.range T, ((∫ ω, Y 0 ω ∂μ) - Y t ω)^2 ∂μ) = _
    rw [expected_fixed_prefix_decomposition μ Y hY hlaw hb T]
    simp
  · rintro z ⟨u, _, rfl⟩
    change _ ≤ (∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ)
    rw [expected_fixed_prefix_decomposition μ Y hY hlaw hb T]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg T) (sq_nonneg _))

/-- Produced expected-fixed minimum; zero horizon has no uniqueness claim. -/
theorem expectedFixedMinimum_eq_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedMinimum μ Y T = (T : ℝ) * variance (Y 0) μ := by
  unfold expectedFixedMinimum
  exact (expected_fixed_prefix_minimum μ Y hY hlaw hb T).2.csInf_eq

/-- Independent-prediction consumer; actual strict-past producers follow. -/
theorem iid_cumulative_prediction_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, MemLp (prediction t) 2 μ)
    (hInd : ∀ t, IndepFun (prediction t) (Y t) μ) (T : ℕ) :
    (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
      (T : ℝ) * variance (Y 0) μ =
        ∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
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

/-- Legal-input measurable history policy: a.s. feasibility and independence are derived. -/
theorem history_policy_expectedFixed_excess {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t z ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedRegret μ Y (fun t ω => policy t (fun i => Y i ω)) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y (fun t ω => policy t (fun i => Y i ω)) T := by
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

/-- Actual first-half strict-past meanPredict: a.s. support produces L2 without pointwise strengthening. -/
theorem meanPredict_expectedFixed_excess {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ) (T : ℕ) :
    expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T := by
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

/-- The distribution-known mean attains the expected fixed benchmark; not an unknown-law learner. -/
theorem constant_mean_expectedFixed_excess_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      expectedFixedRegret μ Y (fun _ _ => ∫ ω, Y 0 ω ∂μ) T = 0 := by
  refine ⟨(expected_fixed_prefix_minimum μ Y hY hlaw hb T).1, ?_⟩
  unfold expectedFixedRegret
  rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T,
    expected_fixed_prefix_decomposition μ Y hY hlaw hb T]
  simp

/-- Positive-horizon finite normalization; no asymptotic convergence is asserted. -/
theorem history_policy_normalized_expectedFixed_excess {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t z ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T) :
    (∫ ω, ∑ t ∈ Finset.range T, (policy t (fun i => Y i ω) - Y t ω)^2 ∂μ) /
        (T : ℝ) - variance (Y 0) μ =
      expectedFixedRegret μ Y (fun t ω => policy t (fun i => Y i ω)) T / (T : ℝ) := by
  unfold expectedFixedRegret
  rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
  exact normalized_excess _ _ T hT

end BanditRL.OnlineLearning
