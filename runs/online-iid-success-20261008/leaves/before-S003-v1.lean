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

end BanditRL.OnlineLearning
