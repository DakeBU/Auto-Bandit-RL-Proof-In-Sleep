import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

/-!
Derived squared-loss identities for the Orabona v10 Chapter 1 motivation, printed p.1 / PDF p.13; these are not additional numbered source theorems. Probability and L2 hypotheses are explicit. The random-prediction identity consumes current-target independence; deriving causal independence requires separate information/history producers. These generic identities do not represent all stochastic strategies or prove a learning rate.
-/

namespace BanditRL.OnlineLearning

/-- Chapter 1 squared-loss motivation: the mean minimizes expected squared loss. -/
theorem expected_square_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (u : ℝ) :
    (∫ ω, (u - Y ω)^2 ∂μ) = variance Y μ + (u - ∫ ω, Y ω ∂μ)^2 := by
  have hv := variance_eq_sub ((memLp_const u).sub hY)
  change variance (fun ω => u - Y ω) μ = _ at hv
  rw [variance_const_sub hY.aestronglyMeasurable u] at hv
  have hi : (∫ ω, u - Y ω ∂μ) = u - ∫ ω, Y ω ∂μ := by
    rw [integral_sub (integrable_const u) (hY.integrable (by norm_num))]
    simp
  change variance Y μ = (∫ ω, (u - Y ω)^2 ∂μ) - (∫ ω, u - Y ω ∂μ)^2 at hv
  rw [hi] at hv
  linarith

/-- Current-target independence is the information condition needed for random predictions. -/
theorem independent_prediction_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Y : Ω → ℝ)
    (hP : MemLp P 2 μ) (hY : MemLp Y 2 μ) (h : IndepFun P Y μ) :
    (∫ ω, (P ω - Y ω)^2 ∂μ) =
      (∫ ω, (P ω - ∫ ω, Y ω ∂μ)^2 ∂μ) + variance Y μ := by
  have hv := variance_eq_sub (hP.sub hY)
  rw [variance_sub hP hY, h.covariance_eq_zero hP hY] at hv
  have hc := variance_eq_sub (hP.sub (memLp_const (∫ ω, Y ω ∂μ)))
  change variance (fun ω => P ω - (∫ ω, Y ω ∂μ)) μ = _ at hc
  rw [variance_sub_const hP.aestronglyMeasurable] at hc
  have hi : (∫ ω, P ω - Y ω ∂μ) = (∫ ω, P ω ∂μ) - ∫ ω, Y ω ∂μ :=
    integral_sub (hP.integrable (by norm_num)) (hY.integrable (by norm_num))
  have hj : (∫ ω, P ω - (∫ ω, Y ω ∂μ) ∂μ) =
      (∫ ω, P ω ∂μ) - ∫ ω, Y ω ∂μ := by
    rw [integral_sub (hP.integrable (by norm_num)) (integrable_const _)]
    simp
  change variance P μ - 2 * 0 + variance Y μ =
    (∫ ω, (P ω - Y ω)^2 ∂μ) - (∫ ω, P ω - Y ω ∂μ)^2 at hv
  change variance P μ = (∫ ω, (P ω - (∫ ω, Y ω ∂μ))^2 ∂μ) -
    (∫ ω, P ω - (∫ ω, Y ω ∂μ) ∂μ)^2 at hc
  rw [hi] at hv
  rw [hj] at hc
  linarith

end BanditRL.OnlineLearning
