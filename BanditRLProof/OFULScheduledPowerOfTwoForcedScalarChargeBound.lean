import BanditRLProof.OFULScheduledPowerOfTwoForcedAllTimeConfidence

/-!
# Scalar forced-action charge for power-of-two scheduled OFUL

This module replaces the explicit prescribed-action charge in the all-time
power-of-two forced OFUL theorem by a logarithmic scalar budget. The probability
space, policy, and all-time confidence event are inherited unchanged from the
upstream leaf.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set

namespace BanditRLProof
namespace OFUL

universe u

/-- A pointwise prescribed-arm gap ceiling bounds the forced charge by its cardinality. -/
theorem powerOfTwoForcedActionSuccessorPseudoRegret_le_card_mul
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    (horizon : Nat)
    (forcedGapBound : Real)
    (hforcedGap : forall exponent,
      linearValue thetaStar (actionFeature best) -
          linearValue thetaStar (actionFeature (forcedAction exponent)) <=
        forcedGapBound) :
    powerOfTwoForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction horizon <=
      ((powerOfTwoForcedIndexSet horizon).card : Real) *
        forcedGapBound := by
  have hsum :=
    Finset.sum_le_card_nsmul
      (powerOfTwoForcedIndexSet horizon)
      (fun n =>
        linearValue thetaStar (actionFeature best) -
          linearValue thetaStar
            (actionFeature (forcedAction (Nat.log2 (n + 1)))))
      forcedGapBound
      (fun n _hn => hforcedGap (Nat.log2 (n + 1)))
  simpa only [
    powerOfTwoForcedActionSuccessorPseudoRegret,
    nsmul_eq_mul,
    Nat.cast_ofNat] using hsum

/-- The forced charge is at most `Nat.log2 horizon + 1` times a gap ceiling. -/
theorem powerOfTwoForcedActionSuccessorPseudoRegret_le_log2_add_one_mul
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    (horizon : Nat)
    (forcedGapBound : Real)
    (hforcedGapBound : 0 <= forcedGapBound)
    (hforcedGap : forall exponent,
      linearValue thetaStar (actionFeature best) -
          linearValue thetaStar (actionFeature (forcedAction exponent)) <=
        forcedGapBound) :
    powerOfTwoForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction horizon <=
      ((Nat.log2 horizon + 1 : Nat) : Real) * forcedGapBound := by
  calc
    powerOfTwoForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction horizon <=
      ((powerOfTwoForcedIndexSet horizon).card : Real) * forcedGapBound :=
        powerOfTwoForcedActionSuccessorPseudoRegret_le_card_mul
          thetaStar actionFeature best forcedAction horizon
          forcedGapBound hforcedGap
    _ <= ((Nat.log2 horizon + 1 : Nat) : Real) * forcedGapBound := by
      apply mul_le_mul_of_nonneg_right _ hforcedGapBound
      exact_mod_cast card_powerOfTwoForcedIndexSet_le_log2_add_one horizon

/--
The standard parameter and arm envelopes instantiate the generic gap ceiling
for every prescribed arm.
-/
theorem
    powerOfTwoForcedActionSuccessorPseudoRegret_le_log2_add_one_mul_two_mul_parameterFeatureBound
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (S L2 : Real) (hS : 0 <= S)
    (htheta : euclideanLength thetaStar <= S)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    (horizon : Nat) :
    powerOfTwoForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction horizon <=
      ((Nat.log2 horizon + 1 : Nat) : Real) *
        (2 * S * Real.sqrt L2) := by
  apply
    powerOfTwoForcedActionSuccessorPseudoRegret_le_log2_add_one_mul
      thetaStar actionFeature best forcedAction horizon
      (2 * S * Real.sqrt L2)
  · positivity
  · intro exponent
    exact
      linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
        thetaStar (actionFeature best) (actionFeature (forcedAction exponent))
        S L2 hS htheta
        (hactionFeatureBound best)
        (hactionFeatureBound (forcedAction exponent))

/--
Fully scalar all-horizon violation event for the power-of-two forced policy.
At horizon zero the forced set is empty while `Nat.log2 0 + 1 = 1`, so this
uses a harmless conservative envelope rather than an exact zero charge.
-/
noncomputable def
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory | exists horizon,
    ((Nat.log2 horizon + 1 : Nat) : Real) *
          (2 * S * Real.sqrt L2) +
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2 <
      canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory}

/-- The logarithmic scalar-budget violation event is contained in the explicit-charge event. -/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet_subset
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real) (hS : 0 <= S)
    (htheta : euclideanLength thetaStar <= S)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (forcedAction : Nat -> Fin K)
    (best : Fin K) :
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best ⊆
      powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 forcedAction best := by
  intro trajectory htrajectory
  rcases htrajectory with ⟨horizon, hviolation⟩
  refine ⟨horizon, ?_⟩
  exact lt_of_le_of_lt
    (by
      have hcharge :=
        powerOfTwoForcedActionSuccessorPseudoRegret_le_log2_add_one_mul_two_mul_parameterFeatureBound
          thetaStar actionFeature S L2 hS htheta hactionFeatureBound
          best forcedAction horizon
      linarith)
    hviolation

/--
Complete all-horizon theorem with the prescribed-action charge replaced by the
logarithmic power-of-two count and the common linear arm-gap envelope.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_scalarAllHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    (forall horizon trajectory,
      0 <= canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory) ∧
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 best) <=
        ENNReal.ofReal delta := by
  have hbase :=
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS forcedAction environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
  constructor
  · exact hbase.1
  · calc
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 best) <=
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 forcedAction best) := by
        exact measure_mono
          (powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet_subset
            lambda thetaStar actionFeature R delta S L2 hS
            source.theta_norm_le hactionFeatureBound forcedAction best)
      _ <= ENNReal.ofReal delta := hbase.2

end OFUL
end BanditRLProof
