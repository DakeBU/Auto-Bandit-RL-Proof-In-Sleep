import BanditRLProof.OFULScheduledPositiveActionCostBudgetExhaustionExpectedRegret
import BanditRLProof.OFULScheduledCumulativeAlignedWindowPositiveCostBudgetExhaustionExpectedRegret

/-!
# Scheduled OFUL expected regret under a.e. aligned-window positive action costs

This module replaces the earlier pointwise reach contract on every theoretical
trajectory by the measure-theoretically sufficient almost-everywhere contract
under the canonical generated trajectory law. It then specializes the route to
deterministic Nat-valued action costs.

For a probability measure, the aligned-window contract is inconsistent when
`window = 0`, since every block is empty. At `budget = 0`, budget exhaustion is
immediate and the numerical round factor is one; the final uniform wrapper
still accepts the aligned-window contract, while the generic a.e.-reach
terminal can prove that zero-budget edge without it.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

namespace OFUL

/--
An almost-everywhere deterministic bound supplies the local square-integrable
finite-stopping contract. Values outside the support may remain unbounded.
-/
theorem squareIntegrableFiniteStoppingTime_of_bounded_ae
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (tau : Omega -> WithTop Nat)
    (htau : IsStoppingTime F tau)
    (bound : Nat)
    (htau_le : ∀ᵐ omega ∂mu, tau omega <= (bound : WithTop Nat)) :
    SquareIntegrableFiniteStoppingTime mu tau := by
  have hrounds_measurable :
      Measurable
        (fun omega =>
          (((tau omega).untopA + 1 : Nat) : Real)) :=
    (measurable_of_countable
      (fun count : Nat => (((count + 1 : Nat) : Nat) : Real))).comp
        htau.measurable'.untopA
  refine ⟨?_, ?_⟩
  · filter_upwards [htau_le] with omega hle
    intro htop
    simp [htop] at hle
  · refine MemLp.of_bound hrounds_measurable.aestronglyMeasurable
      (((bound + 1 : Nat) : Real)) ?_
    filter_upwards [htau_le] with omega hle
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.succ_le_succ
      (WithTop.untopA_le hle)

/--
The exact round-count second moment obeys the same numerical square bound when
the stopping-time bound is only almost everywhere.
-/
theorem stoppingTimeRoundSecondMoment_le_sq_of_bounded_ae
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (tau : Omega -> WithTop Nat)
    (hstop : SquareIntegrableFiniteStoppingTime mu tau)
    (bound : Nat)
    (htau_le : ∀ᵐ omega ∂mu, tau omega <= (bound : WithTop Nat)) :
    stoppingTimeRoundSecondMoment mu tau hstop <=
      (((bound + 1 : Nat) : Real)) ^ 2 := by
  unfold stoppingTimeRoundSecondMoment
  have hsquare :
      Integrable
        (fun omega =>
          ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) mu :=
    hstop.memLp_rounds.integrable_sq
  have hconst :
      Integrable
        (fun _omega : Omega => (((bound + 1 : Nat) : Real)) ^ 2) mu :=
    integrable_const _
  calc
    integral mu
        (fun omega =>
          ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) <=
        integral mu
          (fun _omega : Omega => (((bound + 1 : Nat) : Real)) ^ 2) := by
      apply integral_mono_ae hsquare hconst
      filter_upwards [htau_le] with omega hle
      apply
        (sq_le_sq₀
          (Nat.cast_nonneg ((tau omega).untopA + 1))
          (Nat.cast_nonneg (bound + 1))).2
      have hnat :
          (tau omega).untopA + 1 <= bound + 1 :=
        Nat.succ_le_succ (WithTop.untopA_le hle)
      exact Nat.cast_le.2 hnat
    _ = (((bound + 1 : Nat) : Real)) ^ 2 := by
      rw [integral_const]
      simp [MeasureTheory.probReal_univ]

end OFUL

namespace Budget

/--
Almost-everywhere resource reach gives an almost-everywhere deterministic bound
on the first budget-exhaustion time.
-/
theorem budgetExhaustionTime_le_reachHorizon_ae_of_spent_reach
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (spent : Nat -> Omega -> Nat)
    (budget reachHorizon : Nat)
    (hreach : ∀ᵐ omega ∂mu, budget <= spent reachHorizon omega) :
    ∀ᵐ omega ∂mu,
      budgetExhaustionTime spent budget omega <=
        (reachHorizon : WithTop Nat) := by
  filter_upwards [hreach] with omega hreachOmega
  unfold budgetExhaustionTime
  exact
    MeasureTheory.hittingAfter_le_of_mem
      (Nat.zero_le reachHorizon) hreachOmega

/--
An adapted budget-exhaustion time reached almost surely by a deterministic
horizon is square-integrable under every finite measure.
-/
theorem
    squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon_ae
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget reachHorizon : Nat)
    (hspent : Adapted F spent)
    (hreach : ∀ᵐ omega ∂mu, budget <= spent reachHorizon omega) :
    OFUL.SquareIntegrableFiniteStoppingTime
      mu (budgetExhaustionTime spent budget) := by
  exact
    OFUL.squareIntegrableFiniteStoppingTime_of_bounded_ae
      mu (budgetExhaustionTime spent budget)
      (isStoppingTime_budgetExhaustionTime_of_adapted budget hspent)
      reachHorizon
      (budgetExhaustionTime_le_reachHorizon_ae_of_spent_reach
        mu spent budget reachHorizon hreach)

/--
The round-count second moment of budget exhaustion reached almost surely by
`reachHorizon` is at most `(reachHorizon + 1)^2`.
-/
theorem
    stoppingTimeRoundSecondMoment_budgetExhaustionTime_le_of_reachHorizon_ae
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget reachHorizon : Nat)
    (hspent : Adapted F spent)
    (hreach : ∀ᵐ omega ∂mu, budget <= spent reachHorizon omega) :
    let tau := budgetExhaustionTime spent budget
    let hstop :=
      squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon_ae
        mu spent budget reachHorizon hspent hreach
    OFUL.stoppingTimeRoundSecondMoment mu tau hstop <=
      (((reachHorizon + 1 : Nat) : Real)) ^ 2 := by
  dsimp only
  exact
    OFUL.stoppingTimeRoundSecondMoment_le_sq_of_bounded_ae
      mu (budgetExhaustionTime spent budget)
      (squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon_ae
        mu spent budget reachHorizon hspent hreach)
      reachHorizon
      (budgetExhaustionTime_le_reachHorizon_ae_of_spent_reach
        mu spent budget reachHorizon hreach)

/--
Canonical scheduled OFUL expected pseudo-regret when budget exhaustion occurs
by a deterministic reach horizon almost surely under the canonical measure.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_reachHorizonRoundsSq_add_initialGap_mul_reachHorizonRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime_reachedBy_ae
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
    (hreach :
      ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
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
      ∀ᵐ trajectory ∂mu,
        tau trajectory <= (reachHorizon : WithTop Nat) := by
    exact
      budgetExhaustionTime_le_reachHorizon_ae_of_spent_reach
        mu spent budget reachHorizon hreach
  have hstop :
      OFUL.SquareIntegrableFiniteStoppingTime mu tau := by
    exact
      squareIntegrableFiniteStoppingTime_budgetExhaustionTime_of_reachHorizon_ae
        mu spent budget reachHorizon hspent hreach
  have hmoment :
      integral mu
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        (((reachHorizon + 1 : Nat) : Real)) ^ 2 := by
    simpa only [OFUL.stoppingTimeRoundSecondMoment] using
      (OFUL.stoppingTimeRoundSecondMoment_le_sq_of_bounded_ae
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
Almost every trajectory selects an action with positive deterministic cost at
least once in every aligned half-open block.
-/
def AlignedWindowPositiveActionCostAE
    {K : Nat}
    (mu : Measure (Nat -> Fin K × Real))
    (actionCost : Fin K -> Nat)
    (window : Nat) : Prop :=
  ∀ᵐ trajectory ∂mu, forall block,
    exists s,
      s ∈ Finset.Ico (block * window) ((block + 1) * window) /\
        1 <= actionCost (trajectory s).1

/--
The all-block a.e. contract is equivalent to proving the selected positive-cost
witness almost surely for each natural block separately.
-/
theorem alignedWindowPositiveActionCostAE_iff_forall_ae
    {K : Nat}
    (mu : Measure (Nat -> Fin K × Real))
    (actionCost : Fin K -> Nat)
    (window : Nat) :
    AlignedWindowPositiveActionCostAE mu actionCost window ↔
      forall block,
        ∀ᵐ trajectory ∂mu,
          exists s,
            s ∈ Finset.Ico (block * window) ((block + 1) * window) /\
              1 <= actionCost (trajectory s).1 := by
  rw [AlignedWindowPositiveActionCostAE, ae_all_iff]

/--
One positive selected-action cost in each aligned block makes the whole block
sum positive almost surely.
-/
theorem
    canonicalActionCostProcess_alignedWindowPositive_ae
    {K : Nat}
    (mu : Measure (Nat -> Fin K × Real))
    (actionCost : Fin K -> Nat)
    (window : Nat)
    (hwindow : AlignedWindowPositiveActionCostAE
      mu actionCost window) :
    ∀ᵐ trajectory ∂mu, forall block,
      1 <=
        (Finset.Ico (block * window) ((block + 1) * window)).sum
          (fun s => canonicalActionCostProcess actionCost s trajectory) := by
  filter_upwards [hwindow] with trajectory htrajectory
  intro block
  obtain ⟨s, hs, hpositive⟩ := htrajectory block
  calc
    1 <= canonicalActionCostProcess actionCost s trajectory := by
      simpa only [canonicalActionCostProcess] using hpositive
    _ <=
        (Finset.Ico (block * window) ((block + 1) * window)).sum
          (fun t => canonicalActionCostProcess actionCost t trajectory) := by
      exact
        Finset.single_le_sum
          (fun t _ht => Nat.zero_le
            (canonicalActionCostProcess actionCost t trajectory))
          hs

/--
The a.e. aligned selected-action contract reaches cumulative action-cost budget
by completed round `budget * window`.
-/
theorem budget_le_cumulativeActionCost_budget_mul_ae
    {K : Nat}
    (mu : Measure (Nat -> Fin K × Real))
    (actionCost : Fin K -> Nat)
    (window budget : Nat)
    (hwindow : AlignedWindowPositiveActionCostAE
      mu actionCost window) :
    ∀ᵐ trajectory ∂mu,
      budget <=
        cumulativeActionCost actionCost (budget * window) trajectory := by
  have haligned :=
    canonicalActionCostProcess_alignedWindowPositive_ae
      mu actionCost window hwindow
  filter_upwards [haligned] with trajectory htrajectory
  let fixedCost : Nat -> Unit -> Nat :=
    fun s _ => canonicalActionCostProcess actionCost s trajectory
  have hfixed :
      forall block (_point : Unit),
        1 <=
          (Finset.Ico (block * window) ((block + 1) * window)).sum
            (fun s => fixedCost s ()) := by
    intro block _point
    simpa only [fixedCost] using htrajectory block
  have hreached :=
    budget_le_cumulativeSpent_budget_mul_of_alignedWindowPositive
      fixedCost window budget hfixed ()
  simpa only [
      cumulativeActionCost,
      cumulativeSpent,
      fixedCost,
      canonicalActionCostProcess] using hreached

/--
Canonical scheduled OFUL expected pseudo-regret stopped at deterministic
selected-action cost budget exhaustion under an a.e. aligned-window positive
cost contract.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetWindowRoundsSq_add_initialGap_mul_budgetWindowRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_aeAlignedWindowPositiveActionCostBudgetExhaustionTime
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
    (window budget : Nat)
    (hwindow : AlignedWindowPositiveActionCostAE
      (Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      actionCost window) :
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
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_reachHorizonRoundsSq_add_initialGap_mul_reachHorizonRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime_reachedBy_ae
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
      (cumulativeActionCost actionCost) budget (budget * window)
      (adapted_cumulativeActionCost actionCost)
      (budget_le_cumulativeActionCost_budget_mul_ae
        (Thompson.canonicalHistoryTrajectoryMeasure
          (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment)
        actionCost window budget hwindow)

end Budget
end BanditRLProof
