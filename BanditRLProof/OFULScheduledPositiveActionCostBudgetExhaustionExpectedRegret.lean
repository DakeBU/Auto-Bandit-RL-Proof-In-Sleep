import BanditRLProof.OFULScheduledCumulativePositiveCostBudgetExhaustionExpectedRegret

/-!
# Scheduled OFUL expected regret under positive action costs

This module specializes the cumulative positive-cost budget-exhaustion route
to a deterministic Nat-valued cost on the finite action set. At round `t`, the
cost process reads the current action from the canonical generated trajectory.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u

namespace Budget

/-- The deterministic cost of the current canonical trajectory action. -/
def canonicalActionCostProcess
    {K : Nat}
    (actionCost : Fin K -> Nat)
    (t : Nat)
    (trajectory : Nat -> Fin K × Real) : Nat :=
  actionCost (trajectory t).1

/--
The current-action cost is adapted to the canonical all-round filtration:
the current trajectory coordinate is measurable, as are all maps between
countable measurable spaces.
-/
theorem adapted_canonicalActionCostProcess
    {K : Nat}
    (actionCost : Fin K -> Nat) :
    Adapted
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      (canonicalActionCostProcess actionCost) := by
  intro t
  exact
    (measurable_of_countable actionCost).comp
      (measurable_fst.comp
        (OFUL.measurable_canonicalHistoryTrajectory_coordinate_allRound
          (K := K) (t := t) (horizon := t) le_rfl))

/-- Positive arm costs give a pointwise positive trajectory cost process. -/
theorem canonicalActionCostProcess_one_le
    {K : Nat}
    (actionCost : Fin K -> Nat)
    (hpositive : forall action, 1 <= actionCost action) :
    forall t trajectory, 1 <= canonicalActionCostProcess actionCost t trajectory := by
  intro t trajectory
  exact hpositive (trajectory t).1

/--
Action cost spent after `t` completed rounds, using the half-open index set
`{0, ..., t - 1}`.
-/
def cumulativeActionCost
    {K : Nat}
    (actionCost : Fin K -> Nat)
    (t : Nat)
    (trajectory : Nat -> Fin K × Real) : Nat :=
  cumulativeSpent (canonicalActionCostProcess actionCost) t trajectory

@[simp]
theorem cumulativeActionCost_apply
    {K : Nat}
    (actionCost : Fin K -> Nat)
    (t : Nat)
    (trajectory : Nat -> Fin K × Real) :
    cumulativeActionCost actionCost t trajectory =
      (Finset.range t).sum (fun s => actionCost (trajectory s).1) :=
  rfl

/-- The half-open cumulative action-cost process remains adapted. -/
theorem adapted_cumulativeActionCost
    {K : Nat}
    (actionCost : Fin K -> Nat) :
    Adapted
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      (cumulativeActionCost actionCost) := by
  simpa only [cumulativeActionCost] using
    adapted_cumulativeSpent
      (adapted_canonicalActionCostProcess actionCost)

/-- Positive arm costs make cumulative action cost grow by at least one. -/
theorem cumulativeActionCost_unitGrowth_of_one_le
    {K : Nat}
    (actionCost : Fin K -> Nat)
    (hpositive : forall action, 1 <= actionCost action) :
    forall t trajectory,
      cumulativeActionCost actionCost t trajectory + 1 <=
        cumulativeActionCost actionCost (t + 1) trajectory := by
  simpa only [cumulativeActionCost] using
    cumulativeSpent_unitGrowth_of_one_le
      (canonicalActionCostProcess actionCost)
      (canonicalActionCostProcess_one_le actionCost hpositive)

/--
Canonical scheduled OFUL expected pseudo-regret stopped when the half-open
cumulative deterministic action cost reaches the budget.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetRoundsSq_add_initialGap_mul_budgetRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_positiveActionCostBudgetExhaustionTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : OFUL.IsOptimalLinearArm thetaStar actionFeature best)
    (source : OFUL.CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment)
    (actionCost : Fin K -> Nat)
    (budget : Nat)
    (hpositive : forall action, 1 <= actionCost action) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let tau := budgetExhaustionTime (cumulativeActionCost actionCost) budget
    let stoppedRegret :=
      stoppedValue
        (fun horizon trajectory =>
          OFUL.canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau
    let bad :=
      OFUL.telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau
    0 <= integral mu stoppedRegret /\
      integral mu stoppedRegret <=
        OFUL.telescopingHighProbabilityPseudoRegretQuadraticCoefficient
            (Feature := Feature) R delta lambda S L2 *
          (((budget + 1 : Nat) : Real)) ^ 2 +
        OFUL.standardScalarInitialGapBound S L2 *
          (((budget + 1 : Nat) : Real)) * Real.sqrt delta /\
      mu bad <= ENNReal.ofReal delta := by
  simpa only [cumulativeActionCost] using
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetRoundsSq_add_initialGap_mul_budgetRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_cumulativePositiveCostBudgetExhaustionTime
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
      (canonicalActionCostProcess actionCost) budget
      (adapted_canonicalActionCostProcess actionCost)
      (canonicalActionCostProcess_one_le actionCost hpositive)

end Budget
end BanditRLProof
