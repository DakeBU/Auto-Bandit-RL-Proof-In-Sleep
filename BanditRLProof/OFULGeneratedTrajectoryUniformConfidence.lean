import BanditRLProof.OFULGeneratedTrajectoryConfidenceGap

/-!
# Canonical generated-trajectory uniform confidence for OFUL

This module packages the precise filtration and conditional-law contracts
needed to apply the compiled finite-window scalar-ridge confidence theorem to
one canonical history-algorithm trajectory. It then combines that probability
bound with the compiled successor-window good-event gap transport.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u

namespace BanditRLProof
namespace OFUL

/--
Regularity source needed to apply scalar-ridge uniform confidence to one
canonical history-algorithm trajectory.

The selected feature is the actual canonical action feature. Constructing this
source from a concrete reward environment therefore remains a genuine
predictability and conditional-law obligation.
-/
structure CanonicalScalarRidgeConfidenceSource
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R S : Real)
    (horizon : Nat) where
  filtration :
    Filtration Nat
      (inferInstance : MeasurableSpace (Nat -> Fin K × Real))
  noise : Nat -> (Nat -> Fin K × Real) -> Real
  projectionBound : EuclideanSpace Real Feature -> Nat -> Real
  theta_norm_le : euclideanLength thetaStar <= S
  feature_stronglyMeasurable : forall i j,
    StronglyMeasurable[filtration i] (fun trajectory =>
      canonicalHistoryTrajectoryFeature actionFeature i trajectory j)
  noise_stronglyAdapted :
    StronglyAdapted filtration (fun t trajectory =>
      match t with
      | 0 => 0
      | i + 1 => noise i trajectory)
  projectionBound_nonneg : forall theta i,
    0 <= projectionBound theta i
  projection_le : forall theta i trajectory,
    |dotProduct (WithLp.ofLp theta)
        (canonicalHistoryTrajectoryFeature actionFeature i trajectory)| <=
      projectionBound theta i
  noise_hasCondSubgaussianMGF : forall i, i < horizon ->
    ProbabilityTheory.HasCondSubgaussianMGF
      (filtration i) (filtration.le i) (noise i)
      (constantSquaredVarianceProxy R i)
      (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment)
  response_eq : forall trajectory i, i < horizon ->
    canonicalHistoryTrajectoryResponse i trajectory =
      dotProduct thetaStar
        (canonicalHistoryTrajectoryFeature actionFeature i trajectory) +
      noise i trajectory

/--
The generic equal-share scalar-ridge confidence theorem specialized to one
canonical history-algorithm trajectory.
-/
theorem
    measure_canonicalHistoryTrajectory_uniformScalarRidgeConfidenceFailureSet_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (S : Real)
    (horizon : Nat)
    (source : CanonicalScalarRidgeConfidenceSource
      algorithm environment thetaStar actionFeature R S horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
        (finiteHorizonUniformScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse
          R delta horizon) <=
      ENNReal.ofReal delta := by
  exact
    measure_finiteHorizonUniformScalarRidgeConfidenceFailureSet_le
      (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment)
      lambda hlambda thetaStar S source.theta_norm_le
      source.filtration
      (canonicalHistoryTrajectoryFeature actionFeature)
      canonicalHistoryTrajectoryResponse
      source.noise
      R hR source.projectionBound
      source.feature_stronglyMeasurable
      source.noise_stronglyAdapted
      source.projectionBound_nonneg
      source.projection_le
      horizon source.noise_hasCondSubgaussianMGF
      source.response_eq
      delta hdelta hdelta_one

/--
Strict violation of the compiled successor-window OFUL good-event gap bound.
The range index `n` is charged to the actual action at time `n + 1`, so time
zero is not part of this event.
-/
def canonicalHistoryTrajectorySumRangeSuccGapViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (horizon : Nat)
    (comparator : Nat -> Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory |
    (Finset.range horizon).sum (fun n =>
        2 *
          finiteHorizonScalarConfidenceRadius
            (canonicalHistoryTrajectoryFeature actionFeature)
            R (delta / ((horizon + 1 : Nat) : Real))
            lambda S (n + 1) trajectory *
          confidenceWidth
            (finiteHorizonScalarGram lambda
              (canonicalHistoryTrajectoryFeature actionFeature)
              (n + 1) trajectory)
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) <
      (Finset.range horizon).sum (fun n =>
        linearValue thetaStar (actionFeature (comparator (n + 1))) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1))))}

/--
Canonical high-probability successor-gap theorem. Under the exact generated
feature/noise/response regularity source, the probability that the cumulative
true linear gap over rounds `1, ..., horizon` exceeds the compiled
radius-times-width sum is at most the total confidence budget `delta`.
-/
theorem
    measure_canonicalHistoryTrajectorySumRangeSuccGapViolationSet_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (comparator : Nat -> Fin K)
    (source : CanonicalScalarRidgeConfidenceSource
      (finiteHistoryScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R
          (delta / ((horizon + 1 : Nat) : Real)) S)
      environment thetaStar actionFeature R S horizon) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S horizon comparator) <=
      ENNReal.ofReal delta := by
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R
        (delta / ((horizon + 1 : Nat) : Real)) S
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let failureSet :=
    finiteHorizonUniformScalarRidgeConfidenceFailureSet
      lambda thetaStar S
      (canonicalHistoryTrajectoryFeature actionFeature)
      canonicalHistoryTrajectoryResponse
      R delta horizon
  have hfailure : mu failureSet <= ENNReal.ofReal delta := by
    exact
      measure_canonicalHistoryTrajectory_uniformScalarRidgeConfidenceFailureSet_le
        algorithm environment lambda hlambda thetaStar actionFeature
        R hR S horizon source delta hdelta hdelta_one
  have hgap :=
    canonicalHistoryTrajectory_sum_range_succ_gap_le_on_uniformConfidence
      hK lambda hlambda thetaStar actionFeature R delta S
      environment horizon comparator
  calc
    mu (canonicalHistoryTrajectorySumRangeSuccGapViolationSet
        lambda thetaStar actionFeature R delta S horizon comparator) <=
        mu failureSet := by
      apply measure_mono_ae
      filter_upwards [hgap] with trajectory htrajectory
      intro hviolation
      by_contra hnotFailure
      exact
        (not_lt_of_ge (htrajectory hnotFailure)) hviolation
    _ <= ENNReal.ofReal delta := hfailure

end OFUL
end BanditRLProof
