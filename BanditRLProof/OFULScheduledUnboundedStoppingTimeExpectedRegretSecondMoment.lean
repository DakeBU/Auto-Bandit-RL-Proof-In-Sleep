import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegretClosed

/-!
# Explicit second-moment unbounded stopping-time OFUL expected-regret rate

This module integrates the quadratic stopped-budget envelope. The canonical
terminal theorem therefore depends only on the supplied round-count second
moment, not on an unevaluated expected stopped-budget term.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u

/--
The expected stopped explicit telescoping budget is controlled by the same
round-count second moment used by the bad-event overflow bound.
-/
theorem
    integral_stoppedValue_telescopingHighProbabilityPseudoRegretBound_le_quadraticCoefficient_mul_roundSecondMoment_of_squareIntegrableFiniteStoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (mu : Measure (Nat -> Fin K × Real))
    (R : Real) (hR : 0 <= R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (hS : 0 <= S)
    (L2 : Real) (hL2 : 0 <= L2)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (hstop : SquareIntegrableFiniteStoppingTime mu tau)
    (roundSecondMoment : Real)
    (hroundSecondMoment :
      integral mu
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        roundSecondMoment) :
    integral mu
        (stoppedValue
          (fun horizon (_trajectory : Nat -> Fin K × Real) =>
            telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2)
          tau) <=
      telescopingHighProbabilityPseudoRegretQuadraticCoefficient
          (Feature := Feature) R delta lambda S L2 *
        roundSecondMoment := by
  let rounds : (Nat -> Fin K × Real) -> Real := fun trajectory =>
    (((tau trajectory).untopA + 1 : Nat) : Real)
  let coefficient :=
    telescopingHighProbabilityPseudoRegretQuadraticCoefficient
      (Feature := Feature) R delta lambda S L2
  have hbudgetIntegrable :
      Integrable
        (stoppedValue
          (fun horizon (_trajectory : Nat -> Fin K × Real) =>
            telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2)
          tau) mu := by
    exact
      integrable_stoppedValue_telescopingHighProbabilityPseudoRegretBound_of_squareIntegrableFiniteStoppingTime
        (Feature := Feature) mu R hR delta hdelta hdelta_one
        lambda hlambda S hS L2 hL2 tau htau hstop
  have hquadratic :
      Integrable (fun trajectory => rounds trajectory ^ 2) mu := by
    simpa only [rounds] using hstop.memLp_rounds.integrable_sq
  have hcoefficient_nonneg : 0 <= coefficient := by
    dsimp only [coefficient]
    exact
      telescopingHighProbabilityPseudoRegretQuadraticCoefficient_nonneg
        (Feature := Feature) R hR delta hdelta lambda hlambda S hS L2 hL2
  have hdom :
      Integrable
        (fun trajectory => rounds trajectory ^ 2 * coefficient) mu :=
    hquadratic.mul_const coefficient
  have hpoint :
      forall trajectory,
        stoppedValue
            (fun horizon (_trajectory : Nat -> Fin K × Real) =>
              telescopingHighProbabilityPseudoRegretBound
                (Feature := Feature) R delta lambda S horizon L2)
            tau trajectory <=
          rounds trajectory ^ 2 * coefficient := by
    intro trajectory
    simpa only [stoppedValue, rounds, coefficient] using
      (telescopingHighProbabilityPseudoRegretBound_le_rounds_sq_mul_coefficient
        (Feature := Feature) R hR delta hdelta hdelta_one
        lambda hlambda S hS (tau trajectory).untopA L2 hL2)
  calc
    integral mu
        (stoppedValue
          (fun horizon (_trajectory : Nat -> Fin K × Real) =>
            telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2)
          tau) <=
        integral mu
          (fun trajectory => rounds trajectory ^ 2 * coefficient) := by
      exact integral_mono hbudgetIntegrable hdom hpoint
    _ = integral mu (fun trajectory => rounds trajectory ^ 2) *
          coefficient := by
      rw [integral_mul_const]
    _ <= roundSecondMoment * coefficient := by
      exact mul_le_mul_of_nonneg_right hroundSecondMoment hcoefficient_nonneg
    _ = coefficient * roundSecondMoment := by ring

/--
Canonical generated-trajectory unbounded-stopping expected pseudo-regret bound
with every stopped-budget term replaced by an explicit second-moment charge.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_roundSecondMoment_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime
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
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (hstop : SquareIntegrableFiniteStoppingTime
      (Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      tau)
    (roundSecondMoment : Real)
    (hroundSecondMoment :
      integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment)
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        roundSecondMoment) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let stoppedRegret :=
      stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau
    let bad :=
      telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau
    0 <= integral mu stoppedRegret ∧
      integral mu stoppedRegret <=
        telescopingHighProbabilityPseudoRegretQuadraticCoefficient
            (Feature := Feature) R delta lambda S L2 *
          roundSecondMoment +
        standardScalarInitialGapBound S L2 *
          Real.sqrt roundSecondMoment * Real.sqrt delta ∧
      mu bad <= ENNReal.ofReal delta := by
  dsimp only
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R delta S)
      environment
  let stoppedRegret :=
    stoppedValue
      (fun horizon trajectory =>
        canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory)
      tau
  let stoppedBudget :=
    stoppedValue
      (fun horizon (_trajectory : Nat -> Fin K × Real) =>
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2)
      tau
  let bad :=
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
      lambda thetaStar actionFeature R delta S L2 best tau
  have hclosed :
      0 <= integral mu stoppedRegret ∧
        integral mu stoppedRegret <=
          integral mu stoppedBudget +
            standardScalarInitialGapBound S L2 *
              Real.sqrt roundSecondMoment * Real.sqrt delta ∧
        mu bad <= ENNReal.ofReal delta := by
    exact
      integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_integral_stoppedBudget_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime_automaticBudgetIntegrability
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment L2 hL2
        hactionFeatureBound hL2lambda best hbest source tau htau hstop
        roundSecondMoment hroundSecondMoment
  have hbudget :
      integral mu stoppedBudget <=
        telescopingHighProbabilityPseudoRegretQuadraticCoefficient
            (Feature := Feature) R delta lambda S L2 *
          roundSecondMoment := by
    exact
      integral_stoppedValue_telescopingHighProbabilityPseudoRegretBound_le_quadraticCoefficient_mul_roundSecondMoment_of_squareIntegrableFiniteStoppingTime
        (Feature := Feature) mu R hR.le delta hdelta hdelta_one
        lambda hlambda S hS L2 hL2 tau htau hstop
        roundSecondMoment hroundSecondMoment
  rcases hclosed with ⟨hnonneg, hregret, htail⟩
  refine ⟨hnonneg, ?_, htail⟩
  exact hregret.trans
    (add_le_add hbudget le_rfl)

end OFUL
end BanditRLProof
