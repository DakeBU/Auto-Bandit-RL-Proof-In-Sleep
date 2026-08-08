import BanditRLProof.OFULExpectedRegretRate
import BanditRLProof.OFULScheduledBoundedStoppingTimeExpectedRegret

/-!
# Explicit bounded-stopping-time expected OFUL pseudo-regret rate

This module tunes the outer confidence budget of the scheduled bounded
stopping-time expectation theorem to `1 / (T + 1)`. The stopped bad-event
charge becomes one initial-gap envelope, while the scheduled confidence
logarithm remains explicit.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix

universe u

/--
The explicit scheduled confidence logarithm after choosing the outer
expected-regret budget `delta_T = 1 / (T + 1)`.
-/
noncomputable def telescopingStandardExpectedRegretLogBudget
    {Feature : Type u} [Fintype Feature]
    (lambda : Real) (horizon : Nat) (L2 : Real) : Real :=
  standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2 +
    2 * Real.log
      ((((horizon + 1 : Nat) : Real) ^ 2) *
        ((horizon + 2 : Nat) : Real))

/--
Substituting `delta_T = 1 / (T + 1)` into the scheduled confidence logarithm
gives the explicit cubic-in-horizon logarithmic scale.
-/
theorem
    telescopingHighProbabilityRegretLogBudget_standardExpectedRegretDelta
    {Feature : Type u} [Fintype Feature]
    (lambda : Real) (horizon : Nat) (L2 : Real) :
    telescopingHighProbabilityRegretLogBudget
        (Feature := Feature)
        lambda (standardExpectedRegretDelta horizon) horizon L2 =
      telescopingStandardExpectedRegretLogBudget
        (Feature := Feature) lambda horizon L2 := by
  have hscale :
      ((((horizon + 1 : Nat) : Real) *
          ((horizon + 2 : Nat) : Real)) /
          standardExpectedRegretDelta horizon) =
        (((horizon + 1 : Nat) : Real) ^ 2) *
          ((horizon + 2 : Nat) : Real) := by
    unfold standardExpectedRegretDelta
    field_simp
  unfold telescopingHighProbabilityRegretLogBudget
    telescopingStandardExpectedRegretLogBudget
  rw [hscale]

/--
Explicit expected pseudo-regret budget for a stopping time bounded by `T`
under the single scheduled policy tuned with outer budget `1 / (T + 1)`.
-/
noncomputable def telescopingStandardExpectedPseudoRegretBound
    {Feature : Type u} [Fintype Feature]
    (R lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  4 * S * Real.sqrt L2 +
    2 *
      (R * Real.sqrt
          (telescopingStandardExpectedRegretLogBudget
            (Feature := Feature) lambda horizon L2) +
        Real.sqrt lambda * S) *
      (Real.sqrt (((horizon + 1 : Nat) : Real)) *
        Real.sqrt
          (2 *
            standardScalarLogDetBudget
              (Feature := Feature) lambda (horizon + 1) L2))

/--
The endpoint high-probability budget plus the tuned bad-event envelope charge
is exactly the explicit scheduled expected pseudo-regret rate.
-/
theorem
    telescopingHighProbabilityPseudoRegretBound_add_initial_standardExpectedRegretDelta_eq
    {Feature : Type u} [Fintype Feature]
    (R lambda S : Real) (horizon : Nat) (L2 : Real) :
    telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature)
        R (standardExpectedRegretDelta horizon)
        lambda S horizon L2 +
        standardScalarInitialGapBound S L2 =
      telescopingStandardExpectedPseudoRegretBound
        (Feature := Feature) R lambda S horizon L2 := by
  unfold telescopingHighProbabilityPseudoRegretBound
    telescopingStandardExpectedPseudoRegretBound
    standardScalarInitialGapBound
  rw [
    telescopingHighProbabilityRegretLogBudget_standardExpectedRegretDelta
      (Feature := Feature) lambda horizon L2]
  ring

/--
Complete explicit expected pseudo-regret theorem for one bounded stopping time
under the horizon-tuned telescoping-schedule OFUL policy.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_telescopingStandardExpectedBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
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
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat)) :
    let delta := standardExpectedRegretDelta maxHorizon
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
    0 <= integral mu stoppedRegret /\
      integral mu stoppedRegret <=
        telescopingStandardExpectedPseudoRegretBound
          (Feature := Feature) R lambda S maxHorizon L2 := by
  dsimp only
  have h :=
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_endpoint_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      (standardExpectedRegretDelta maxHorizon)
      (standardExpectedRegretDelta_pos maxHorizon)
      (standardExpectedRegretDelta_le_one maxHorizon)
      S hS environment L2 hL2 hactionFeatureBound hL2lambda
      best hbest source tau htau maxHorizon htau_le
  rw [
    standardScalarAllRoundGapEnvelope_mul_standardExpectedRegretDelta,
    telescopingHighProbabilityPseudoRegretBound_add_initial_standardExpectedRegretDelta_eq]
    at h
  exact h

/--
Expected stopped pseudo-regret for the horizon-indexed family of scheduled
policies tuned at `delta_T = 1 / (T + 1)`.
-/
noncomputable def canonicalTelescopingStandardExpectedStoppedPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (best : Fin K)
    (tau : Nat -> (Nat -> Fin K × Real) -> WithTop Nat)
    (maxHorizon : Nat) : Real :=
  integral
    (Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R
          (standardExpectedRegretDelta maxHorizon) S)
      environment)
    (stoppedValue
      (fun horizon trajectory =>
        canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory)
      (tau maxHorizon))

/--
The named horizon-indexed expected stopped pseudo-regret is nonnegative and
bounded pointwise by the explicit tuned scheduled rate.
-/
theorem
    canonicalTelescopingStandardExpectedStoppedPseudoRegret_nonneg_and_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
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
    (tau : Nat -> (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : forall maxHorizon,
      IsStoppingTime
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        (tau maxHorizon))
    (htau_le : forall maxHorizon trajectory,
      tau maxHorizon trajectory <= (maxHorizon : WithTop Nat))
    (maxHorizon : Nat) :
    0 <= canonicalTelescopingStandardExpectedStoppedPseudoRegret
      hK lambda thetaStar actionFeature R S environment best tau maxHorizon /\
      canonicalTelescopingStandardExpectedStoppedPseudoRegret
          hK lambda thetaStar actionFeature R S environment best tau maxHorizon <=
        telescopingStandardExpectedPseudoRegretBound
          (Feature := Feature) R lambda S maxHorizon L2 := by
  simpa [canonicalTelescopingStandardExpectedStoppedPseudoRegret] using
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_telescopingStandardExpectedBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR S hS environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
      (tau maxHorizon) (htau maxHorizon) maxHorizon
      (htau_le maxHorizon)

end OFUL
end BanditRLProof
