import BanditRLProof.OFULScheduledUnitGrowthBudgetExhaustionExpectedRegret

/-!
# Scheduled OFUL expected regret under cumulative positive costs

This module constructs an adapted Nat-valued resource process by summing
per-round costs over completed rounds. Pointwise positive costs give the
unit-growth contract required by the compiled budget-exhaustion OFUL theorem.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

namespace Budget

/--
Resource spent after `t` completed rounds, using the half-open index set
`{0, ..., t - 1}`.
-/
def cumulativeSpent
    {Omega : Type v}
    (cost : Nat -> Omega -> Nat)
    (t : Nat)
    (omega : Omega) : Nat :=
  (Finset.range t).sum fun s => cost s omega

@[simp]
theorem cumulativeSpent_zero
    {Omega : Type v}
    (cost : Nat -> Omega -> Nat)
    (omega : Omega) :
    cumulativeSpent cost 0 omega = 0 := by
  simp [cumulativeSpent]

@[simp]
theorem cumulativeSpent_succ
    {Omega : Type v}
    (cost : Nat -> Omega -> Nat)
    (t : Nat)
    (omega : Omega) :
    cumulativeSpent cost (t + 1) omega =
      cumulativeSpent cost t omega + cost t omega := by
  simp [cumulativeSpent, Finset.sum_range_succ]

/--
Finite prefix sums of an adapted per-round Nat-valued cost process remain
adapted. A cost observed at `s < t` is promoted from `F s` to `F t`.
-/
theorem adapted_cumulativeSpent
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    {F : Filtration Nat mOmega}
    {cost : Nat -> Omega -> Nat}
    (hcost : Adapted F cost) :
    Adapted F (cumulativeSpent cost) := by
  intro t
  unfold cumulativeSpent
  exact Finset.measurable_sum (Finset.range t) fun s hs =>
    hcost.measurable_le
      (Nat.le_of_lt (Finset.mem_range.mp hs))

/--
If every completed round costs at least one, cumulative spend grows by at
least one at each step.
-/
theorem cumulativeSpent_unitGrowth_of_one_le
    {Omega : Type v}
    (cost : Nat -> Omega -> Nat)
    (hcost : forall t omega, 1 <= cost t omega) :
    forall t omega,
      cumulativeSpent cost t omega + 1 <=
        cumulativeSpent cost (t + 1) omega := by
  intro t omega
  rw [cumulativeSpent_succ]
  exact Nat.add_le_add_left (hcost t omega) _

/--
Canonical expected pseudo-regret bound for the single telescoping-schedule
OFUL policy stopped when the cumulative positive per-round cost reaches the
budget.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetRoundsSq_add_initialGap_mul_budgetRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_cumulativePositiveCostBudgetExhaustionTime
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
    (cost : Nat -> (Nat -> Fin K × Real) -> Nat)
    (budget : Nat)
    (hcost : Adapted
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      cost)
    (hpositive : forall t trajectory, 1 <= cost t trajectory) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let tau := budgetExhaustionTime (cumulativeSpent cost) budget
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
  exact
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetRoundsSq_add_initialGap_mul_budgetRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime_of_unitGrowth
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
      (cumulativeSpent cost) budget
      (adapted_cumulativeSpent hcost)
      (cumulativeSpent_unitGrowth_of_one_le cost hpositive)

end Budget
end BanditRLProof
