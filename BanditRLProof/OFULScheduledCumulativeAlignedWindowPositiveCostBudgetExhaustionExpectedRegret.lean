import BanditRLProof.OFULScheduledCumulativePositiveCostBudgetExhaustionExpectedRegret

/-!
# Scheduled OFUL expected regret under aligned-window positive costs

This module separates a resource threshold from the deterministic horizon by
which it is reached. It then allows individual rounds to have zero cost while
requiring every aligned block of a fixed length to spend at least one unit.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

namespace Budget

/--
If accumulated resource reaches `budget` by `reachHorizon`, its first
budget-exhaustion time is pointwise at most `reachHorizon`.
-/
theorem budgetExhaustionTime_le_reachHorizon_of_spent_reach
    {Omega : Type v}
    (spent : Nat -> Omega -> Nat)
    (budget reachHorizon : Nat)
    (hreach : forall omega, budget <= spent reachHorizon omega) :
    forall omega,
      budgetExhaustionTime spent budget omega <=
        (reachHorizon : WithTop Nat) := by
  intro omega
  unfold budgetExhaustionTime
  exact
    MeasureTheory.hittingAfter_le_of_mem
      (Nat.zero_le reachHorizon) (hreach omega)

/--
An adapted budget-exhaustion time reached by an arbitrary deterministic
horizon is square-integrable under every finite measure.
-/
theorem squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget reachHorizon : Nat)
    (hspent : Adapted F spent)
    (hreach : forall omega, budget <= spent reachHorizon omega) :
    OFUL.SquareIntegrableFiniteStoppingTime
      mu (budgetExhaustionTime spent budget) := by
  exact
    OFUL.squareIntegrableFiniteStoppingTime_of_bounded
      mu (budgetExhaustionTime spent budget)
      (isStoppingTime_budgetExhaustionTime_of_adapted budget hspent)
      reachHorizon
      (budgetExhaustionTime_le_reachHorizon_of_spent_reach
        spent budget reachHorizon hreach)

/--
The round-count second moment of a budget-exhaustion time reached by
`reachHorizon` is at most `(reachHorizon + 1)^2`.
-/
theorem
    stoppingTimeRoundSecondMoment_budgetExhaustionTime_le_of_reachHorizon
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget reachHorizon : Nat)
    (hspent : Adapted F spent)
    (hreach : forall omega, budget <= spent reachHorizon omega) :
    let tau := budgetExhaustionTime spent budget
    let hstop :=
      squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon
        mu spent budget reachHorizon hspent hreach
    OFUL.stoppingTimeRoundSecondMoment mu tau hstop <=
      (((reachHorizon + 1 : Nat) : Real)) ^ 2 := by
  dsimp only
  exact
    OFUL.stoppingTimeRoundSecondMoment_le_sq_of_bounded
      mu (budgetExhaustionTime spent budget)
      (squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon
        mu spent budget reachHorizon hspent hreach)
      reachHorizon
      (budgetExhaustionTime_le_reachHorizon_of_spent_reach
        spent budget reachHorizon hreach)

/--
Canonical scheduled OFUL expected pseudo-regret when budget exhaustion is
known to occur by a separately supplied deterministic reach horizon.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_reachHorizonRoundsSq_add_initialGap_mul_reachHorizonRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime_reachedBy
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
    (budget reachHorizon : Nat)
    (hspent : Adapted
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      spent)
    (hreach : forall trajectory,
      budget <= spent reachHorizon trajectory) :
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
          (((reachHorizon + 1 : Nat) : Real)) ^ 2 +
        OFUL.standardScalarInitialGapBound S L2 *
          (((reachHorizon + 1 : Nat) : Real)) * Real.sqrt delta /\
      mu bad <= ENNReal.ofReal delta := by
  dsimp only
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R delta S)
      environment
  let tau := budgetExhaustionTime spent budget
  have htau :
      IsStoppingTime
        (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        tau := by
    exact isStoppingTime_budgetExhaustionTime_of_adapted budget hspent
  have hbound :
      forall trajectory,
        tau trajectory <= (reachHorizon : WithTop Nat) := by
    exact
      budgetExhaustionTime_le_reachHorizon_of_spent_reach
        spent budget reachHorizon hreach
  have hstop :
      OFUL.SquareIntegrableFiniteStoppingTime mu tau := by
    exact
      squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon
        mu spent budget reachHorizon hspent hreach
  have hmoment :
      integral mu
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        (((reachHorizon + 1 : Nat) : Real)) ^ 2 := by
    simpa only [OFUL.stoppingTimeRoundSecondMoment] using
      (OFUL.stoppingTimeRoundSecondMoment_le_sq_of_bounded
        mu tau hstop reachHorizon hbound)
  have hterminal :=
    OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_roundSecondMoment_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source tau htau hstop
      ((((reachHorizon + 1 : Nat) : Real)) ^ 2) hmoment
  simpa only [Real.sqrt_sq (Nat.cast_nonneg (reachHorizon + 1))] using
    hterminal

/--
If every aligned block of length `window` costs at least one, cumulative spend
after `block * window` completed rounds is at least `block`.
-/
theorem block_le_cumulativeSpent_mul_of_alignedWindowPositive
    {Omega : Type v}
    (cost : Nat -> Omega -> Nat)
    (window : Nat)
    (haligned : forall block omega,
      1 <=
        (Finset.Ico (block * window) ((block + 1) * window)).sum
          (fun s => cost s omega)) :
    forall block omega,
      block <= cumulativeSpent cost (block * window) omega := by
  intro block
  induction block with
  | zero =>
      intro omega
      exact Nat.zero_le _
  | succ block ih =>
      intro omega
      have hle :
          block * window <= (block + 1) * window :=
        Nat.mul_le_mul_right window (Nat.le_succ block)
      have hsplit :
          cumulativeSpent cost (block * window) omega +
              (Finset.Ico (block * window) ((block + 1) * window)).sum
                (fun s => cost s omega) =
            cumulativeSpent cost ((block + 1) * window) omega := by
        exact
          Finset.sum_range_add_sum_Ico
            (fun s => cost s omega) hle
      have hresult :
          block + 1 <=
            cumulativeSpent cost ((block + 1) * window) omega := by
        calc
          block + 1 <=
              cumulativeSpent cost (block * window) omega + 1 :=
            Nat.add_le_add_right (ih omega) 1
          _ <=
              cumulativeSpent cost (block * window) omega +
                (Finset.Ico (block * window) ((block + 1) * window)).sum
                  (fun s => cost s omega) :=
            Nat.add_le_add_left (haligned block omega) _
          _ = cumulativeSpent cost ((block + 1) * window) omega :=
            hsplit
      simpa [Nat.succ_eq_add_one] using hresult

/--
Aligned-window positivity reaches resource threshold `budget` by completed
round `budget * window`.
-/
theorem budget_le_cumulativeSpent_budget_mul_of_alignedWindowPositive
    {Omega : Type v}
    (cost : Nat -> Omega -> Nat)
    (window budget : Nat)
    (haligned : forall block omega,
      1 <=
        (Finset.Ico (block * window) ((block + 1) * window)).sum
          (fun s => cost s omega)) :
    forall omega,
      budget <= cumulativeSpent cost (budget * window) omega :=
  block_le_cumulativeSpent_mul_of_alignedWindowPositive
    cost window haligned budget

/--
Canonical scheduled OFUL expected pseudo-regret under aligned-window positive
costs. Individual rounds may have zero cost; the deterministic reach horizon
is `budget * window`.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetWindowRoundsSq_add_initialGap_mul_budgetWindowRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_cumulativeAlignedWindowPositiveCostBudgetExhaustionTime
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
    (window budget : Nat)
    (hcost : Adapted
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      cost)
    (haligned : forall block trajectory,
      1 <=
        (Finset.Ico (block * window) ((block + 1) * window)).sum
          (fun s => cost s trajectory)) :
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
          (((budget * window + 1 : Nat) : Real)) ^ 2 +
        OFUL.standardScalarInitialGapBound S L2 *
          (((budget * window + 1 : Nat) : Real)) * Real.sqrt delta /\
      mu bad <= ENNReal.ofReal delta := by
  exact
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_reachHorizonRoundsSq_add_initialGap_mul_reachHorizonRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime_reachedBy
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
      (cumulativeSpent cost) budget (budget * window)
      (adapted_cumulativeSpent hcost)
      (budget_le_cumulativeSpent_budget_mul_of_alignedWindowPositive
        cost window budget haligned)

end Budget
end BanditRLProof
