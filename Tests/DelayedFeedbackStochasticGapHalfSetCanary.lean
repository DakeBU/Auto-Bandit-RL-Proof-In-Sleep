import BanditRLProof.DelayedFeedback.StochasticGapHalfSet

open BanditRLProof

namespace BanditRLProof.DelayedFeedback

/-- The generic theorem really includes the empty family rather than relying
on a hidden `Nonempty (Fin K)` assumption. -/
example :
    2 * (aboveTwiceAverageGap (K := 0) (fun i => Fin.elim0 i)).card <= 0 := by
  exact two_mul_card_aboveTwiceAverageGap_le
    (K := 0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- Zero average is handled without cancelling or dividing by the average. -/
example :
    aboveTwiceAverageGap (K := 4) (fun _ => (0 : Real)) = ∅ := by
  norm_num [aboveTwiceAverageGap, finiteAverageGap]

/-- A signed regression canary guards the explicit nonnegativity premise.  It
does not make or promote a claim about an intended source correction. -/
example :
    ¬ (2 * (aboveTwiceAverageGap (K := 2)
      (fun _ => (-1 : Real))).card <= 2) := by
  norm_num [aboveTwiceAverageGap, finiteAverageGap, Fin.sum_univ_succ]

/-- A concrete source-shaped loss instance: only the largest of four gaps is
strictly above twice the average. -/
example :
    (aboveTwiceAverageGap (K := 4)
      (sourceStochasticLossGap
        (fun i => ![(0 : Real), 1, 1, 6] i) (0 : Fin 4))).card = 1 := by
  rw [show aboveTwiceAverageGap (K := 4)
      (sourceStochasticLossGap
        (fun i => ![(0 : Real), 1, 1, 6] i) (0 : Fin 4)) = {3} by
    ext i
    fin_cases i <;>
      norm_num [aboveTwiceAverageGap, finiteAverageGap,
        sourceStochasticLossGap, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk.injEq] <;>
      decide]
  simp

/-- The source-shaped specialization consumes only optimality of the selected
minimum-mean arm; it does not receive a prepackaged nonnegativity premise. -/
example :
    2 * (aboveTwiceAverageGap (K := 4)
      (sourceStochasticLossGap
        (fun i => ![(0 : Real), 1, 1, 6] i) (0 : Fin 4))).card <= 4 := by
  apply two_mul_card_sourceStochasticLossGap_aboveTwiceAverage_le
  intro i
  fin_cases i <;> norm_num

#check finiteAverageGap
#check aboveTwiceAverageGap
#check two_mul_card_aboveTwiceAverageGap_le
#check sourceStochasticLossGap
#check sourceStochasticLossGap_nonneg
#check two_mul_card_sourceStochasticLossGap_aboveTwiceAverage_le

#print axioms two_mul_card_aboveTwiceAverageGap_le
#print axioms sourceStochasticLossGap_nonneg
#print axioms two_mul_card_sourceStochasticLossGap_aboveTwiceAverage_le

end BanditRLProof.DelayedFeedback
