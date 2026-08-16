import Mathlib.Tactic

open Real

namespace BanditRLProof.LowerBounds

noncomputable def gaussianMinimaxGap
    (alternativeCount horizon : Real) : Real :=
  Real.sqrt (alternativeCount / (4 * horizon))

theorem gaussianMinimaxGap_sq
    {alternativeCount horizon : Real}
    (halternatives : 0 ≤ alternativeCount) (hhorizon : 0 ≤ horizon) :
    gaussianMinimaxGap alternativeCount horizon ^ 2 =
      alternativeCount / (4 * horizon) := by
  rw [gaussianMinimaxGap, sq_sqrt]
  positivity

theorem gaussianMinimaxGap_informationExponent_eq_half
    {alternativeCount horizon : Real}
    (halternatives : 0 < alternativeCount) (hhorizon : 0 < horizon) :
    2 * horizon * gaussianMinimaxGap alternativeCount horizon ^ 2 /
        alternativeCount = 1 / 2 := by
  rw [gaussianMinimaxGap_sq halternatives.le hhorizon.le]
  field_simp
  ring

theorem gaussianMinimaxGap_le_half
    {alternativeCount horizon : Real}
    (hhorizon : 0 < horizon) (hcount_le : alternativeCount ≤ horizon) :
    gaussianMinimaxGap alternativeCount horizon ≤ 1 / 2 := by
  rw [gaussianMinimaxGap]
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · have hdiv : alternativeCount / horizon ≤ 1 :=
      (div_le_one hhorizon).mpr hcount_le
    have hfour : alternativeCount / (4 * horizon) ≤ 1 / 4 := by
      calc
        alternativeCount / (4 * horizon) =
            (alternativeCount / horizon) / 4 := by field_simp
        _ ≤ 1 / 4 := by linarith
    norm_num at hfour ⊢
    exact hfour

end BanditRLProof.LowerBounds
