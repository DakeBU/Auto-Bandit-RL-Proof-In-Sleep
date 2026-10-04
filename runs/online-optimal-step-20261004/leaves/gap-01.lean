import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace BanditRL.OnlineOptimalStep

noncomputable def upperBound (A B η : ℝ) : ℝ := A / (2 * η) + η * B / 2
noncomputable def optimalStep (A B : ℝ) : ℝ := Real.sqrt A / Real.sqrt B

theorem gap_identity (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) :
    upperBound A B η - Real.sqrt A * Real.sqrt B =
      (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η) := by
  have hAsq := Real.sq_sqrt hA
  have hBsq := Real.sq_sqrt hB
  dsimp [upperBound]
  field_simp [ne_of_gt hη]
  linear_combination -hAsq - η ^ 2 * hBsq

end BanditRL.OnlineOptimalStep
