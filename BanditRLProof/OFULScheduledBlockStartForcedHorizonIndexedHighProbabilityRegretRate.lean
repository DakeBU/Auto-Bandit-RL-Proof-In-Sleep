import BanditRLProof.OFULScheduledBlockStartForcedHorizonWindowFiniteHorizonTail

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set

namespace BanditRLProof
namespace OFUL

/--
Canonical trajectory measure of the member indexed by `horizon` in the
horizon-window forced-policy family.
-/
noncomputable def blockStartForcedHorizonIndexedCanonicalTrajectoryMeasure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedActionAtHorizon : Nat -> Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) :
    Measure (Nat -> Fin K × Real) :=
  Thompson.canonicalHistoryTrajectoryMeasure
    (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
      hK lambda actionFeature R delta S
      (forcedActionAtHorizon horizon) horizon)
    environment

/-- Unfold the policy and window selected by the outer horizon index. -/
theorem blockStartForcedHorizonIndexedCanonicalTrajectoryMeasure_apply
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedActionAtHorizon : Nat -> Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) :
    blockStartForcedHorizonIndexedCanonicalTrajectoryMeasure
        hK lambda actionFeature R delta S
        forcedActionAtHorizon environment horizon =
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
          hK lambda actionFeature R delta S
          (forcedActionAtHorizon horizon) horizon)
        environment := by
  rfl

/-- One-envelope fixed-horizon bad-event family. -/
noncomputable def
    blockStartForcedHorizonIndexedCanonicalStandardHighProbabilityPseudoRegretViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K) :
    Nat -> Set (Nat -> Fin K × Real) :=
  fun horizon =>
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet
      lambda thetaStar actionFeature R delta S L2 horizon best

/-- Unfold the one-envelope bad event selected by the outer horizon index. -/
theorem
    blockStartForcedHorizonIndexedCanonicalStandardHighProbabilityPseudoRegretViolationSet_apply
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K)
    (horizon : Nat) :
    blockStartForcedHorizonIndexedCanonicalStandardHighProbabilityPseudoRegretViolationSet
        lambda thetaStar actionFeature R delta S L2 best horizon =
      blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet
        lambda thetaStar actionFeature R delta S L2 horizon best := by
  rfl

/--
Every positive member of the horizon-indexed forced-policy family has the
one-envelope fixed-horizon pseudo-regret tail. Each member has its own measure.
-/
theorem
    blockStartForcedHorizonIndexedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (forcedActionAtHorizon : Nat -> Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    forall horizon, 0 < horizon ->
      (forall trajectory,
        0 <= canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory) ∧
        blockStartForcedHorizonIndexedCanonicalTrajectoryMeasure
            hK lambda actionFeature R delta S
            forcedActionAtHorizon environment horizon
            (blockStartForcedHorizonIndexedCanonicalStandardHighProbabilityPseudoRegretViolationSet
              lambda thetaStar actionFeature R delta S L2 best horizon) <=
          ENNReal.ofReal delta := by
  intro horizon hhorizon
  simpa only [
    blockStartForcedHorizonIndexedCanonicalTrajectoryMeasure_apply,
    blockStartForcedHorizonIndexedCanonicalStandardHighProbabilityPseudoRegretViolationSet_apply] using
    (blockStartForcedCanonicalStandardHighProbabilityPseudoRegret_horizonWindow_nonneg_and_finiteHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS
      (forcedActionAtHorizon horizon) horizon hhorizon environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source)

end OFUL
end BanditRLProof
