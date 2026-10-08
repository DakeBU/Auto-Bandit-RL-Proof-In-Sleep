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

end BanditRL.OnlineLearning
