import BanditRLProof
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Textbook Part IV Chapter 13 public canary

This external root-import canary exercises the compiled Chapter 13 semantic
and deterministic interfaces. It deliberately does not claim the
unit-variance Gaussian minimax lower bound stated as Theorem 13.1: the source
defers that proof to Chapter 15, and the required history change-of-measure
bridge remains planned for Chapters 14--15.
-/

namespace BanditRLProof.TextbookPartIVChapter13Canary

open scoped BigOperators ENNReal
open LowerBounds

section MinimaxSurface

example (regret : Fin 2 -> Fin 2 -> ENNReal) :
    minimaxExpectedRegret regret Set.univ Set.univ ≤
      worstCaseExpectedRegret regret Set.univ (0 : Fin 2) := by
  exact minimaxExpectedRegret_le_worstCaseExpectedRegret
    regret Set.univ Set.univ 0 (Set.mem_univ 0)

example (regret : Fin 2 -> Fin 2 -> ENNReal) :
    regret (0 : Fin 2) (1 : Fin 2) ≤
      worstCaseExpectedRegret regret Set.univ 0 := by
  exact expectedRegret_le_worstCaseExpectedRegret
    regret Set.univ 0 1 (Set.mem_univ 1)

example (regret : Fin 2 -> Fin 2 -> ENNReal) (lower : ENNReal)
    (hlower : ∀ policy : (Set.univ : Set (Fin 2)),
      lower ≤ worstCaseExpectedRegret regret Set.univ policy.1) :
    lower ≤ minimaxExpectedRegret regret Set.univ Set.univ := by
  exact le_minimaxExpectedRegret regret Set.univ Set.univ lower hlower

end MinimaxSurface

section LeastExploredAlternative

/-- A nondegenerate three-arm witness: expected pulls `(4,1,1)` sum to horizon six. -/
example :
    ∃ i : Fin 2,
      (![4, 1, 1] : Fin 3 -> Real) i.succ ≤ (6 : Real) / (2 : Real) := by
  apply exists_leastExploredAlternative (m := 2) (horizon := 6)
      (expectedPulls := ![4, 1, 1])
  · norm_num
  · intro arm
    fin_cases arm <;> norm_num
  · norm_num [Fin.sum_univ_succ]

end LeastExploredAlternative

section ConditionalTwoEnvironmentAlgebra

/--
The numeric instance exposes a nonzero cross-environment pull discrepancy:
`3 - 2 <= 1`. No information-theoretic theorem is smuggled into the canary.
-/
example :
    (1 : Real) * ((6 : Real) - 1) / 2 ≤
      max (baseEnvironmentRegret 6 1 3)
        (changedEnvironmentRegretLowerBound 1 2) := by
  exact max_base_changed_regretLowerBound_ge_half_sub_error 6 1 3 2 1
    (by norm_num) (by norm_num)

/-- The zero-error directional interface remains available as a corollary. -/
example :
    (1 : Real) * (6 : Real) / 2 ≤
      max (baseEnvironmentRegret 6 1 2)
        (changedEnvironmentRegretLowerBound 1 3) := by
  exact max_base_changed_regretLowerBound_ge_half 6 1 2 3
    (by norm_num) (by norm_num)

end ConditionalTwoEnvironmentAlgebra

#print axioms LowerBounds.worstCaseExpectedRegret
#print axioms LowerBounds.minimaxExpectedRegret
#print axioms LowerBounds.expectedRegret_le_worstCaseExpectedRegret
#print axioms LowerBounds.minimaxExpectedRegret_le_worstCaseExpectedRegret
#print axioms LowerBounds.le_minimaxExpectedRegret
#print axioms LowerBounds.exists_alternative_le_average
#print axioms LowerBounds.alternativeExpectedPullBudget_le
#print axioms LowerBounds.exists_leastExploredAlternative
#print axioms LowerBounds.baseEnvironmentRegret
#print axioms LowerBounds.changedEnvironmentRegretLowerBound
#print axioms LowerBounds.max_base_changed_regretLowerBound_ge_half_sub_error
#print axioms LowerBounds.max_base_changed_regretLowerBound_ge_half

end BanditRLProof.TextbookPartIVChapter13Canary
