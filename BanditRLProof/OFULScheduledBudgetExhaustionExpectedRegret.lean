import BanditRLProof.BudgetStoppingTime
import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegretExactMoment

/-!
# Scheduled OFUL expected regret at budget exhaustion

This module connects the Mathlib-backed budget hitting time to the single
telescoping-schedule OFUL policy. A pathwise reach-by-budget premise supplies a
deterministic stopping bound, hence the square-integrable stopping contract and
an explicit round-count second-moment bound.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

namespace OFUL

/--
A stopping time bounded by a deterministic natural horizon has the local
square-integrable finite-stopping contract under any finite measure.
-/
theorem squareIntegrableFiniteStoppingTime_of_bounded
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (tau : Omega -> WithTop Nat)
    (htau : IsStoppingTime F tau)
    (bound : Nat)
    (htau_le : forall omega, tau omega <= (bound : WithTop Nat)) :
    SquareIntegrableFiniteStoppingTime mu tau := by
  have hrounds_measurable :
      Measurable
        (fun omega =>
          (((tau omega).untopA + 1 : Nat) : Real)) :=
    (measurable_of_countable
      (fun count : Nat => (((count + 1 : Nat) : Nat) : Real))).comp
        htau.measurable'.untopA
  refine ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun omega htop => by
      have hle := htau_le omega
      simp [htop] at hle
  · refine MemLp.of_bound hrounds_measurable.aestronglyMeasurable
      (((bound + 1 : Nat) : Real)) ?_
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.succ_le_succ
        (WithTop.untopA_le (htau_le omega))

/--
The exact second moment of a deterministically bounded square-integrable
stopping time is at most the square of the corresponding round-count bound.
-/
theorem stoppingTimeRoundSecondMoment_le_sq_of_bounded
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (tau : Omega -> WithTop Nat)
    (hstop : SquareIntegrableFiniteStoppingTime mu tau)
    (bound : Nat)
    (htau_le : forall omega, tau omega <= (bound : WithTop Nat)) :
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
      exact integral_mono hsquare hconst fun omega => by
        apply
          (sq_le_sq₀
            (Nat.cast_nonneg ((tau omega).untopA + 1))
            (Nat.cast_nonneg (bound + 1))).2
        have hnat :
            (tau omega).untopA + 1 <= bound + 1 :=
          Nat.succ_le_succ
            (WithTop.untopA_le (htau_le omega))
        exact Nat.cast_le.2 hnat
    _ = (((bound + 1 : Nat) : Real)) ^ 2 := by
      rw [integral_const]
      simp [MeasureTheory.probReal_univ]

end OFUL

namespace Budget

/--
If the accumulated resource has reached `budget` by index `budget`, its first
budget-exhaustion time is pointwise at most `budget`.
-/
theorem budgetExhaustionTime_le_budget_of_spent_budget
    {Omega : Type v}
    (spent : Nat -> Omega -> Nat)
    (budget : Nat)
    (hreach : forall omega, budget <= spent budget omega) :
    forall omega,
      budgetExhaustionTime spent budget omega <= (budget : WithTop Nat) := by
  intro omega
  unfold budgetExhaustionTime
  exact
    MeasureTheory.hittingAfter_le_of_mem
      (Nat.zero_le budget) (hreach omega)

/--
An adapted budget-exhaustion time reached by index `budget` is a
square-integrable finite stopping time under every finite measure.
-/
theorem squareIntegrableFiniteStoppingTime_budgetExhaustionTime
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget : Nat)
    (hspent : Adapted F spent)
    (hreach : forall omega, budget <= spent budget omega) :
    OFUL.SquareIntegrableFiniteStoppingTime
      mu (budgetExhaustionTime spent budget) := by
  exact
    OFUL.squareIntegrableFiniteStoppingTime_of_bounded
      mu (budgetExhaustionTime spent budget)
      (isStoppingTime_budgetExhaustionTime_of_adapted budget hspent)
      budget
      (budgetExhaustionTime_le_budget_of_spent_budget
        spent budget hreach)

/--
The exact round-count second moment of the reached-by-budget exhaustion time is
at most `(budget + 1)^2`.
-/
theorem stoppingTimeRoundSecondMoment_budgetExhaustionTime_le
    {Omega : Type v} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (spent : Nat -> Omega -> Nat)
    (budget : Nat)
    (hspent : Adapted F spent)
    (hreach : forall omega, budget <= spent budget omega) :
    let tau := budgetExhaustionTime spent budget
    let hstop :=
      squareIntegrableFiniteStoppingTime_budgetExhaustionTime
        mu spent budget hspent hreach
    OFUL.stoppingTimeRoundSecondMoment mu tau hstop <=
      (((budget + 1 : Nat) : Real)) ^ 2 := by
  dsimp only
  exact
    OFUL.stoppingTimeRoundSecondMoment_le_sq_of_bounded
      mu (budgetExhaustionTime spent budget)
      (squareIntegrableFiniteStoppingTime_budgetExhaustionTime
        mu spent budget hspent hreach)
      budget
      (budgetExhaustionTime_le_budget_of_spent_budget
        spent budget hreach)

/--
Canonical expected pseudo-regret bound for the single telescoping-schedule
OFUL policy stopped at a reached-by-budget resource exhaustion time.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_budgetRoundsSq_add_initialGap_mul_budgetRounds_mul_sqrt_delta_and_stoppedViolation_measure_le_of_budgetExhaustionTime
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
    (hreach : forall trajectory, budget <= spent budget trajectory) :
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
    0 <= integral mu stoppedRegret ∧
      integral mu stoppedRegret <=
        OFUL.telescopingHighProbabilityPseudoRegretQuadraticCoefficient
            (Feature := Feature) R delta lambda S L2 *
          (((budget + 1 : Nat) : Real)) ^ 2 +
        OFUL.standardScalarInitialGapBound S L2 *
          (((budget + 1 : Nat) : Real)) * Real.sqrt delta ∧
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
      forall trajectory, tau trajectory <= (budget : WithTop Nat) := by
    exact
      budgetExhaustionTime_le_budget_of_spent_budget
        spent budget hreach
  have hstop :
      OFUL.SquareIntegrableFiniteStoppingTime mu tau := by
    exact
      squareIntegrableFiniteStoppingTime_budgetExhaustionTime
        mu spent budget hspent hreach
  have hmoment :
      integral mu
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        (((budget + 1 : Nat) : Real)) ^ 2 := by
    simpa only [OFUL.stoppingTimeRoundSecondMoment] using
      (OFUL.stoppingTimeRoundSecondMoment_le_sq_of_bounded
        mu tau hstop budget hbound)
  have hterminal :=
    OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_roundSecondMoment_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source tau htau hstop
      ((((budget + 1 : Nat) : Real)) ^ 2) hmoment
  simpa only [Real.sqrt_sq (Nat.cast_nonneg (budget + 1))] using hterminal

end Budget
end BanditRLProof
