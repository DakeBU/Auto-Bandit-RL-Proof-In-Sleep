import BanditRLProof.OFULScheduledAEAlignedWindowPositiveActionCostBudgetExhaustionExpectedRegret

/-!
# Scheduled OFUL budget exhaustion from block-start forced positive actions

The telescoping-confidence OFUL algorithm is deterministic conditional on its
finite pair history. This module exposes its selected action as a named
history function and transports the canonical successor-action law to an
aligned-window positive-cost contract.

At history index `block * window`, the policy generates trajectory action
`block * window + 1`. Under `2 <= window`, that action lies in the aligned
half-open block. If this selector is a fixed positive-cost `forcedAction block`
for every history, the existing a.e. budget-reach theorem gives exhaustion by
`budget * window` and closes the canonical expected-regret/tail terminal.

The forced-selector equality is an explicit policy-design contract. Ordinary
OFUL score maximization does not establish it, and this module does not modify
the OFUL policy or claim a full bandits-with-knapsacks theorem.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u

namespace OFUL

/-- The action selected by the telescoping-confidence OFUL policy. -/
noncomputable def finiteHistoryTelescopingScalarRidgeOptimisticAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    Fin K :=
  finiteHistoryScheduledScalarRidgeOptimisticAction
    hK lambda actionFeature R (allTimeTelescopingDelta delta) S n history

@[simp]
theorem finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm_policy_apply
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R delta S).policy n history =
        Measure.dirac
          (finiteHistoryTelescopingScalarRidgeOptimisticAction
            hK lambda actionFeature R delta S n history) := by
  exact finiteHistoryOptimisticAlgorithm_policy_apply
    hK
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScheduledScalarRidgeRadius
      actionFeature R (allTimeTelescopingDelta delta) lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    (measurable_finiteHistoryScheduledScalarRidgeOptimisticScore
      lambda actionFeature R (allTimeTelescopingDelta delta) S)
    n history

theorem
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryTelescopingScalarRidgeOptimisticAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      (trajectory (n + 1)).1 =
        finiteHistoryTelescopingScalarRidgeOptimisticAction
          hK lambda actionFeature R delta S n
          (Preorder.frestrictLe n trajectory) := by
  simpa only [
      finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm,
      finiteHistoryScheduledScalarRidgeOptimisticAlgorithm,
      finiteHistoryTelescopingScalarRidgeOptimisticAction,
      Thompson.canonicalHistoryTrajectoryAction,
      Thompson.canonicalHistoryTrajectoryReward] using
    (canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryOptimisticAction
      hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScheduledScalarRidgeRadius
        actionFeature R (allTimeTelescopingDelta delta) lambda S)
      (finiteHistoryFixedActionFeature actionFeature)
      (measurable_finiteHistoryScheduledScalarRidgeOptimisticScore
        lambda actionFeature R (allTimeTelescopingDelta delta) S)
      environment n)

end OFUL

namespace Budget

theorem
    alignedWindowPositiveActionCostAE_of_blockStartTelescopingActionCostPositive
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (actionCost : Fin K -> Nat)
    (window : Nat)
    (hwindow : 2 <= window)
    (hpositive :
      forall block
        (history :
          History.FinitePairHistory
            (Fin K) Real (block * window)),
        1 <= actionCost
          (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAction
            hK lambda actionFeature R delta S
            (block * window) history)) :
    AlignedWindowPositiveActionCostAE
      (Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      actionCost window := by
  rw [alignedWindowPositiveActionCostAE_iff_forall_ae]
  intro block
  have haction :=
    OFUL.canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryTelescopingScalarRidgeOptimisticAction
      hK lambda actionFeature R delta S environment (block * window)
  filter_upwards [haction] with trajectory hactionTrajectory
  refine ⟨block * window + 1, ?_, ?_⟩
  · simp only [Finset.mem_Ico]
    constructor
    · omega
    · rw [Nat.add_mul]
      omega
  · rw [hactionTrajectory]
    exact hpositive block (Preorder.frestrictLe (block * window) trajectory)

theorem
    alignedWindowPositiveActionCostAE_of_blockStartForcedTelescopingAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (actionCost : Fin K -> Nat)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (hwindow : 2 <= window)
    (hforced :
      forall block
        (history :
          History.FinitePairHistory
            (Fin K) Real (block * window)),
        OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAction
            hK lambda actionFeature R delta S
            (block * window) history =
          forcedAction block)
    (hpositive : forall block, 1 <= actionCost (forcedAction block)) :
    AlignedWindowPositiveActionCostAE
      (Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      actionCost window := by
  apply
    alignedWindowPositiveActionCostAE_of_blockStartTelescopingActionCostPositive
      hK lambda actionFeature R delta S environment actionCost window hwindow
  intro block history
  rw [hforced block history]
  exact hpositive block

/--
Canonical scheduled OFUL expected pseudo-regret stopped at action-cost budget
exhaustion when every aligned block contains a history-independent forced
positive-cost action immediately after its block start.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetWindowRoundsSq_add_initialGap_mul_budgetWindowRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_blockStartForcedPositiveActionCostBudgetExhaustionTime
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
    (forcedAction : Nat -> Fin K)
    (window budget : Nat)
    (hwindow : 2 <= window)
    (hforced :
      forall block
        (history :
          History.FinitePairHistory
            (Fin K) Real (block * window)),
        OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAction
            hK lambda actionFeature R delta S
            (block * window) history =
          forcedAction block)
    (hpositive : forall block, 1 <= actionCost (forcedAction block)) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let tau := budgetExhaustionTime
      (cumulativeActionCost actionCost) budget
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
          (((budget * window + 1 : Nat) : Real)) ^ 2 +
        OFUL.standardScalarInitialGapBound S L2 *
          (((budget * window + 1 : Nat) : Real)) * Real.sqrt delta /\
      mu bad <= ENNReal.ofReal delta := by
  exact
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetWindowRoundsSq_add_initialGap_mul_budgetWindowRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_aeAlignedWindowPositiveActionCostBudgetExhaustionTime
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
      actionCost window budget
      (alignedWindowPositiveActionCostAE_of_blockStartForcedTelescopingAction
        hK lambda actionFeature R delta S environment
        actionCost forcedAction window hwindow hforced hpositive)

end Budget
end BanditRLProof
