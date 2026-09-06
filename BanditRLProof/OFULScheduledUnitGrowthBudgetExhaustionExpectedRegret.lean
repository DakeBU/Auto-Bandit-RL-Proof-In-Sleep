import BanditRLProof.OFULScheduledBudgetExhaustionExpectedRegret

/-!
# Scheduled OFUL expected regret under unit resource growth

This module derives the pathwise reach-by-budget premise from the more
primitive contract that the accumulated Nat-valued resource grows by at least
one at every round, then reuses the compiled budget-exhaustion OFUL theorem.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

namespace Budget

/--
If a Nat-valued resource process grows by at least one at every step, then its
value at every index dominates that index.
-/
theorem index_le_spent_of_unitGrowth
    {Omega : Type v}
    (spent : Nat -> Omega -> Nat)
    (hunit : forall t omega,
      spent t omega + 1 <= spent (t + 1) omega) :
    forall t omega, t <= spent t omega := by
  intro t
  induction t with
  | zero =>
      intro omega
      exact Nat.zero_le _
  | succ t ih =>
      intro omega
      exact le_trans (Nat.succ_le_succ (ih omega)) (hunit t omega)

/--
Unit pathwise resource growth makes the budget-exhaustion time at most the
budget index.
-/
theorem budgetExhaustionTime_le_budget_of_unitGrowth
    {Omega : Type v}
    (spent : Nat -> Omega -> Nat)
    (budget : Nat)
    (hunit : forall t omega,
      spent t omega + 1 <= spent (t + 1) omega) :
    forall omega,
      budgetExhaustionTime spent budget omega <= (budget : WithTop Nat) := by
  exact
    budgetExhaustionTime_le_budget_of_spent_budget
      spent budget (index_le_spent_of_unitGrowth spent hunit budget)

/--
An adapted unit-growth resource process has a square-integrable finite
budget-exhaustion time under every finite measure.
-/
theorem squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_unitGrowth
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget : Nat)
    (hspent : Adapted F spent)
    (hunit : forall t omega,
      spent t omega + 1 <= spent (t + 1) omega) :
    OFUL.SquareIntegrableFiniteStoppingTime
      mu (budgetExhaustionTime spent budget) := by
  exact
    squareIntegrableFiniteStoppingTime_budgetExhaustionTime
      mu spent budget hspent
      (index_le_spent_of_unitGrowth spent hunit budget)

/--
The exact round-count second moment of a unit-growth budget-exhaustion time is
at most `(budget + 1)^2`.
-/
theorem
    stoppingTimeRoundSecondMoment_budgetExhaustionTime_le_of_unitGrowth
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget : Nat)
    (hspent : Adapted F spent)
    (hunit : forall t omega,
      spent t omega + 1 <= spent (t + 1) omega) :
    let tau := budgetExhaustionTime spent budget
    let hstop :=
      squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_unitGrowth
        mu spent budget hspent hunit
    OFUL.stoppingTimeRoundSecondMoment mu tau hstop <=
      (((budget + 1 : Nat) : Real)) ^ 2 := by
  simpa only [OFUL.stoppingTimeRoundSecondMoment] using
    (stoppingTimeRoundSecondMoment_budgetExhaustionTime_le
      mu spent budget hspent
      (index_le_spent_of_unitGrowth spent hunit budget))

/--
Canonical expected pseudo-regret bound for the single telescoping-schedule
OFUL policy stopped at the budget-exhaustion time of an adapted unit-growth
resource process.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetRoundsSq_add_initialGap_mul_budgetRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime_of_unitGrowth
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
    (spent : Nat -> (Nat -> Fin K × Real) -> Nat)
    (budget : Nat)
    (hspent : Adapted
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      spent)
    (hunit : forall t trajectory,
      spent t trajectory + 1 <= spent (t + 1) trajectory) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let tau := budgetExhaustionTime spent budget
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
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetRoundsSq_add_initialGap_mul_budgetRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
      spent budget hspent
      (index_le_spent_of_unitGrowth spent hunit budget)

end Budget
end BanditRLProof
