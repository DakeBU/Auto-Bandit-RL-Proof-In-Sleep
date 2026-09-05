import BanditRLProof
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Textbook Part IV Chapter 13 public canary

This external root-import canary exercises the compiled Chapter 13 semantic
and deterministic interfaces, the Gaussian two-point testing companion, and
the unit-variance Gaussian minimax lower bound stated as Theorem 13.1 and
compiled through Chapter 15.  The Chernoff test bound is deliberately not
labeled as the sharper two-sided Mills-ratio Eq. (13.1).
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

example {Policy Environment : Type}
    (regret : Policy -> Environment -> ENNReal)
    (policyClass : Set Policy) (environmentClass : Set Environment)
    (policy : Policy)
    (hpolicy : IsMinimaxOptimal regret policyClass environmentClass policy) :
    policy ∈ policyClass ∧
      worstCaseExpectedRegret regret environmentClass policy =
        minimaxExpectedRegret regret policyClass environmentClass := by
  exact ⟨hpolicy.mem_policyClass, hpolicy.eq_minimaxExpectedRegret⟩

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

section GaussianTwoPointTesting

example : 0 < gaussianSampleMeanVariance 8 := by
  exact gaussianSampleMeanVariance_pos 8 (by norm_num)

example :
    (gaussianIIDObservationLaw 8 1).map (gaussianCoordinateAverage 8) =
      gaussianSampleMeanLaw 8 1 := by
  exact gaussianIIDSampleMeanLaw 8 1 (by norm_num)

example :
    {observation : Real | twoPointGaussianThresholdDecision 2 observation ≠ 0} =
      Set.Ici 1 := by
  simpa using
    (twoPointGaussianThresholdDecision_zero_error_event (gap := (2 : Real)) (by norm_num))

example :
    gaussianSampleMeanZeroErrorProbability 8 1 ≤ Real.exp (-1) := by
  simpa using
    (gaussianSampleMeanZeroErrorProbability_le_exp 8 1 (by norm_num))

example :
    gaussianSampleMeanGapErrorProbability 8 1 ≤ Real.exp (-1) := by
  simpa using
    (gaussianSampleMeanGapErrorProbability_le_exp 8 1 (by norm_num))

example :
    gaussianSampleMeanThresholdRisk 8 1 ≤ Real.exp (-1) := by
  simpa using
    (gaussianSampleMeanThresholdRisk_le_exp 8 1 (by norm_num))

end GaussianTwoPointTesting

example (c x : ℝ) (hc : 0 < c) :
    HasDerivAt (gaussianMillsComparison c)
      (-gaussianMillsComparison c x * (2 * x + 1 / Real.sqrt (x ^ 2 + c))) x :=
  hasDerivAt_gaussianMillsComparison hc

example (x : ℝ) :
    gaussianMillsComparison 2 x * (2 * x + 1 / Real.sqrt (x ^ 2 + 2)) ≤
      Real.exp (-x ^ 2) := gaussianMillsComparison_lower_derivative_bound x

#print axioms LowerBounds.hasDerivAt_gaussianMillsComparison
#print axioms LowerBounds.gaussianMillsComparison_lower_derivative_bound

example (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x ^ 2) / (x + Real.sqrt (x ^ 2 + 2)) ≤
      ∫ t in Set.Ioi x, Real.exp (-t ^ 2) := gaussianMills_lower_integral hx

#print axioms LowerBounds.tendsto_gaussianMillsComparison
#print axioms LowerBounds.gaussianMills_lower_integral

example (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in Set.Ioi x, Real.exp (-t ^ 2)) ≤
      Real.exp (-x ^ 2) / (x + Real.sqrt (x ^ 2 + 4 / Real.pi)) :=
  gaussianMills_upper_integral hx

#print axioms LowerBounds.gaussianMills_upper_integral
#print axioms LowerBounds.gaussianReal_zero_standardized_tail
#print axioms LowerBounds.gaussianSampleMeanZeroErrorProbability_mills_bounds
#print axioms LowerBounds.gaussianSampleMeanZeroErrorProbability_source_bounds

example (n : Nat) (hn : 0 < n) (gap : ℝ) (hg : 0 < gap) :
    let q := (n : ℝ) * gap ^ 2
    Real.sqrt (8 / Real.pi) * Real.exp (-q / 8) /
      (Real.sqrt q + Real.sqrt (q + 16)) ≤ gaussianSampleMeanZeroErrorProbability n gap ∧
    gaussianSampleMeanZeroErrorProbability n gap ≤
      Real.sqrt (8 / Real.pi) * Real.exp (-q / 8) /
        (Real.sqrt q + Real.sqrt (q + 32 / Real.pi)) :=
  gaussianSampleMeanZeroErrorProbability_source_bounds n hn gap hg

example (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ gaussianMillsErrorDerivative (4 / Real.pi) x ↔
      x ≤ (4 / Real.pi - 1) / Real.sqrt (2 - 4 / Real.pi) :=
  gaussianMillsErrorDerivative_source_nonneg_iff hx

#print axioms LowerBounds.hasDerivAt_gaussianMillsError
#print axioms LowerBounds.gaussianMillsErrorDerivative_source_nonneg_iff

#print axioms LowerBounds.worstCaseExpectedRegret
#print axioms LowerBounds.minimaxExpectedRegret
#print axioms LowerBounds.IsMinimaxOptimal
#print axioms LowerBounds.IsMinimaxOptimal.mem_policyClass
#print axioms LowerBounds.IsMinimaxOptimal.eq_minimaxExpectedRegret
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
#print axioms LowerBounds.gaussianSampleMeanVariance
#print axioms LowerBounds.gaussianSampleMeanVariance_pos
#print axioms LowerBounds.gaussianSampleMeanLaw
#print axioms LowerBounds.gaussianIIDObservationLaw
#print axioms LowerBounds.gaussianCoordinateAverage
#print axioms LowerBounds.gaussianIIDSumLaw
#print axioms LowerBounds.gaussianIIDSampleMeanLaw
#print axioms LowerBounds.twoPointGaussianThresholdDecision
#print axioms LowerBounds.twoPointGaussianThresholdDecision_zero_error_event
#print axioms LowerBounds.twoPointGaussianThresholdDecision_gap_error_event
#print axioms LowerBounds.gaussianSampleMeanZeroErrorProbability
#print axioms LowerBounds.gaussianSampleMeanGapErrorProbability
#print axioms LowerBounds.hasSubgaussianMGF_id_gaussianReal_zero
#print axioms LowerBounds.hasSubgaussianMGF_gap_sub_id_gaussianReal
#print axioms LowerBounds.gaussianReal_zero_Ici_le_exp_neg_sq_div_two_variance
#print axioms LowerBounds.gaussianReal_gap_Iio_half_le_exp_neg_sq_div_two_variance
#print axioms LowerBounds.gaussianSampleMeanZeroErrorProbability_le_exp
#print axioms LowerBounds.gaussianSampleMeanGapErrorProbability_le_exp
#print axioms LowerBounds.gaussianSampleMeanThresholdRisk
#print axioms LowerBounds.gaussianSampleMeanThresholdRisk_le_exp
#print axioms LowerBounds.unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt

end BanditRLProof.TextbookPartIVChapter13Canary
