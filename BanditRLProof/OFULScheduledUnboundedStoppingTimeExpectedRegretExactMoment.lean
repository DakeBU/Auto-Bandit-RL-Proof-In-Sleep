import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegretSecondMoment

/-!
# Exact-second-moment unbounded stopping-time OFUL expected-regret rate

This module names the actual second moment of the stopping-time round count and
uses it directly in the canonical terminal theorem. Concrete stopping-rule
analyses can subsequently bound this named quantity without rebuilding the
stopped-regret argument.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

/--
The actual second moment of the real round count `tau.untopA + 1` under the
square-integrable finite-stopping contract.
-/
noncomputable def stoppingTimeRoundSecondMoment
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) (tau : Omega -> WithTop Nat)
    (_hstop : SquareIntegrableFiniteStoppingTime mu tau) : Real :=
  integral mu
    (fun omega => ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2)

/-- The exact stopping-time round-count second moment is nonnegative. -/
theorem stoppingTimeRoundSecondMoment_nonneg
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) (tau : Omega -> WithTop Nat)
    (hstop : SquareIntegrableFiniteStoppingTime mu tau) :
    0 <= stoppingTimeRoundSecondMoment mu tau hstop := by
  exact integral_nonneg fun omega => sq_nonneg
    ((((tau omega).untopA + 1 : Nat) : Real))

/--
Canonical generated-trajectory unbounded-stopping expected pseudo-regret bound
stated directly with the actual round-count second moment.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_stoppingTimeRoundSecondMoment_add_initialGap_mul_sqrt_stoppingTimeRoundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime
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
      tau) :
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
          stoppingTimeRoundSecondMoment mu tau hstop +
        standardScalarInitialGapBound S L2 *
          Real.sqrt (stoppingTimeRoundSecondMoment mu tau hstop) *
            Real.sqrt delta ∧
      mu bad <= ENNReal.ofReal delta := by
  dsimp only
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R delta S)
      environment
  have hmoment :
      integral mu
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        stoppingTimeRoundSecondMoment mu tau hstop := by
    rfl
  exact
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_roundSecondMoment_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source tau htau hstop
      (stoppingTimeRoundSecondMoment mu tau hstop) hmoment

end OFUL
end BanditRLProof
