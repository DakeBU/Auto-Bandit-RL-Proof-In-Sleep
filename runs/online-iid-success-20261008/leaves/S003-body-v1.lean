import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Filter Asymptotics
universe u v
namespace BanditRL.OnlineLearning

/-- Signed centered-total sublinearity is exactly vanishing average excess; eventual positive horizons only. -/
theorem centered_total_sublinear_iff_average (total : ℕ → ℝ) (c : ℝ) :
    (fun T => total T - (T : ℝ) * c) =o[atTop] (fun T : ℕ => (T : ℝ)) ↔
      Tendsto (fun T => total T / (T : ℝ) - c) atTop (nhds (0 : ℝ)) := by
  have hz : ∀ᶠ T : ℕ in atTop,
      (T : ℝ) = 0 → total T - (T : ℝ) * c = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    intro hzero
    exact False.elim ((ne_of_gt (Nat.cast_pos.mpr hT)) hzero)
  have he : (fun T => total T / (T : ℝ) - c) =ᶠ[atTop]
      (fun T => (total T - (T : ℝ) * c) / (T : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    exact normalized_excess (total T) c T hT
  rw [isLittleO_iff_tendsto' hz]
  exact (tendsto_congr' he).symm

/-- Actual jointly measurable private-seed strict-history policy success equivalences; convergence is characterized, not asserted for every policy. -/
theorem randomized_history_policy_success_iff {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t s z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t (s, z) ∈ Set.Icc (0 : ℝ) 1) :
    let prediction := fun t ω => policy t (S ω, fun i => Y i ω)
    (∀ T, 0 ≤ expectedFixedRegret μ Y prediction T) ∧
      ((fun T => expectedFixedRegret μ Y prediction T) =o[atTop]
          (fun T : ℕ => (T : ℝ)) ↔
        Tendsto (fun T => (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) / (T : ℝ) - variance (Y 0) μ) atTop (nhds (0 : ℝ))) ∧
      (Tendsto (fun T => (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) / (T : ℝ) - variance (Y 0) μ) atTop (nhds (0 : ℝ)) ↔
        Tendsto (fun T => (∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) / (T : ℝ)) atTop (nhds (0 : ℝ))) := by
  dsimp only
  let prediction := fun t ω => policy t (S ω, fun i => Y i ω)
  have he (T : ℕ) := randomized_history_policy_expectedFixed_excess
    μ Y hY hlaw hb hind S hS hseed policy hp hpb T
  have hmin (T : ℕ) := expectedFixedMinimum_eq_variance μ Y hY hlaw hb T
  refine ⟨fun T => (he T).2, ?_, ?_⟩
  · have hi := centered_total_sublinear_iff_average
      (fun T => ∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ)
      (variance (Y 0) μ)
    simpa only [expectedFixedRegret, hmin] using hi
  · apply tendsto_congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    rw [normalized_excess _ _ T hT]
    have hx := (he T).1
    unfold expectedFixedRegret at hx
    rw [hmin T] at hx
    exact congrArg (fun x => x / (T : ℝ)) hx

/-- Actual unknown-law initial-half strictpast meanPredict expected-fixed upper from source pathwise Theorem1.3; independence not assumed. -/
theorem meanPredict_expectedFixed_upper {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) :
    expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T ≤ 4 + 4 * Real.log T := by
  let prediction := fun t ω => meanPredict (fun i => Y i ω) t
  let m := ∫ ω, Y 0 ω ∂μ
  have hall : ∀ᵐ ω ∂μ, ∀ t, Y t ω ∈ Set.Icc (0 : ℝ) 1 := ae_all_iff.2 hb
  have hL (t : ℕ) : MemLp (Y t) 2 μ :=
    memLp_of_bounded (hb t) (hY t).aestronglyMeasurable 2
  have hP (t : ℕ) : MemLp (prediction t) 2 μ := by
    apply memLp_of_bounded (a := 0) (b := 1) _
      (meanPredict_measurable Y hY t).aestronglyMeasurable
    filter_upwards [hall] with ω hω
    exact meanPredict_mem (fun i => Y i ω) t (fun i _ => hω i)
  have hPI : Integrable (fun ω => ∑ t ∈ Finset.range T,
      (prediction t ω - Y t ω)^2) μ :=
    integrable_finset_sum (Finset.range T)
      (fun t _ => ((hP t).sub (hL t)).integrable_sq)
  have hCI : Integrable (fun ω => ∑ t ∈ Finset.range T, (m - Y t ω)^2) μ :=
    integrable_finset_sum (Finset.range T)
      (fun t _ => ((memLp_const m).sub (hL t)).integrable_sq)
  have hpath : ∀ᵐ ω ∂μ,
      (∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2) -
        (∑ t ∈ Finset.range T, (m - Y t ω)^2) ≤ 4 + 4 * Real.log T := by
    filter_upwards [hall] with ω hω
    have hmain := theorem_1_3 (fun i => Y i ω) T hT (fun i _ => hω i)
    have hmin := empiricalMean_minimizes (fun i => Y i ω) T hT m
    change (∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2) -
      (∑ t ∈ Finset.range T, (m - Y t ω)^2) ≤ _
    linarith
  have hi := integral_mono_ae (hPI.sub hCI)
    (integrable_const (4 + 4 * Real.log (T : ℝ))) hpath
  rw [integral_sub hPI hCI] at hi
  have hc : (∫ ω, ∑ t ∈ Finset.range T, (m - Y t ω)^2 ∂μ) =
      (T : ℝ) * variance (Y 0) μ := by
    simpa only [m, sub_self, sq_zero, mul_zero, add_zero] using
      expected_fixed_prefix_decomposition μ Y hY hlaw hb T m
  rw [hc] at hi
  unfold expectedFixedRegret
  rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
  simpa [prediction] using hi

end BanditRL.OnlineLearning
