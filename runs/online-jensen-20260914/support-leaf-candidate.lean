import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral

noncomputable section
open Set Filter MeasureTheory
namespace BanditRL.OnlineConvex
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem supporting_functional_ae_eq_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Integrable X μ) (a : E →L[ℝ] ℝ)
    (hle : ∀ᵐ ω ∂μ, a (X ω) ≤ a (∫ ω, X ω ∂μ)) :
    ∀ᵐ ω ∂μ, a (X ω) = a (∫ ω, X ω ∂μ) := by
  apply (integral_eq_iff_of_ae_le (a.integrable_comp hX) (integrable_const _) hle).mp
  rw [a.integral_comp_comm hX]
  simp

end BanditRL.OnlineConvex
