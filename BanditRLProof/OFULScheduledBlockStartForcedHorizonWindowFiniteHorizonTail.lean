import BanditRLProof.OFULScheduledBlockStartForcedActionChargeBound

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set

namespace BanditRLProof
namespace OFUL

/-- A positive horizon used as its own block window has one forced successor index. -/
theorem blockStartForcedIndexSet_horizon_self_eq_singleton
    {horizon : Nat} (hhorizon : 0 < horizon) :
    blockStartForcedIndexSet horizon horizon = {0} := by
  ext n
  simp only [
    blockStartForcedIndexSet,
    Finset.mem_filter,
    Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hn, hmod⟩
    rw [Nat.mod_eq_of_lt hn] at hmod
    exact hmod
  · intro hn
    subst n
    exact ⟨hhorizon, Nat.zero_mod horizon⟩

/-- With `window = horizon > 0`, the forced successor charge is its first gap. -/
theorem blockStartForcedActionSuccessorPseudoRegret_horizon_self
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    {horizon : Nat} (hhorizon : 0 < horizon) :
    blockStartForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction horizon horizon =
      linearValue thetaStar (actionFeature best) -
        linearValue thetaStar (actionFeature (forcedAction 0)) := by
  change
    (blockStartForcedIndexSet horizon horizon).sum
        (fun n =>
          linearValue thetaStar (actionFeature best) -
            linearValue thetaStar
              (actionFeature (forcedAction (n / horizon)))) =
      linearValue thetaStar (actionFeature best) -
        linearValue thetaStar (actionFeature (forcedAction 0))
  rw [blockStartForcedIndexSet_horizon_self_eq_singleton hhorizon]
  simp

/-- The exact horizon-window forced charge is bounded by one linear arm-gap envelope. -/
theorem
    blockStartForcedActionSuccessorPseudoRegret_horizon_self_le_two_mul_parameterFeatureBound
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
    {horizon : Nat} (hhorizon : 0 < horizon) :
    blockStartForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction horizon horizon <=
      2 * S * Real.sqrt L2 := by
  rw [
    blockStartForcedActionSuccessorPseudoRegret_horizon_self
      thetaStar actionFeature best forcedAction hhorizon]
  exact
    linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
      thetaStar (actionFeature best) (actionFeature (forcedAction 0))
      S L2 hS htheta
      (hactionFeatureBound best)
      (hactionFeatureBound (forcedAction 0))

/-- Fixed-horizon scalar violation event for the policy whose block window is that horizon. -/
noncomputable def
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (horizon : Nat)
    (best : Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory |
    2 * S * Real.sqrt L2 +
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2 <
      canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory}

/--
The one-charge fixed-horizon violation event is contained in the exact
forced-charge all-horizon event for the same horizon-window policy.
-/
theorem
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet_subset
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
    {horizon : Nat} (hhorizon : 0 < horizon)
    (best : Fin K) :
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet
        lambda thetaStar actionFeature R delta S L2 horizon best ⊆
      blockStartForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2
        forcedAction horizon best := by
  intro trajectory htrajectory
  refine ⟨horizon, ?_⟩
  exact lt_of_le_of_lt
    (add_le_add
      (blockStartForcedActionSuccessorPseudoRegret_horizon_self_le_two_mul_parameterFeatureBound
        thetaStar actionFeature S L2 hS htheta hactionFeatureBound
        best forcedAction hhorizon)
      (le_refl
        (telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2)))
    htrajectory

/--
Fixed-horizon high-probability pseudo-regret theorem for the horizon-indexed
block-start policy family. The forced charge is one linear arm-gap envelope.
-/
theorem
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegret_horizonWindow_nonneg_and_finiteHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    (forall trajectory,
      0 <= canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory) ∧
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction horizon)
          environment
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet
            lambda thetaStar actionFeature R delta S L2 horizon best) <=
        ENNReal.ofReal delta := by
  have hbase :=
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS forcedAction horizon environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
  constructor
  · exact hbase.1 horizon
  · calc
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction horizon)
          environment
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet
            lambda thetaStar actionFeature R delta S L2 horizon best) <=
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction horizon)
          environment
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2
            forcedAction horizon best) := by
        exact measure_mono
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretHorizonWindowViolationSet_subset
            lambda thetaStar actionFeature R delta S L2 hS
            source.theta_norm_le hactionFeatureBound forcedAction hhorizon best)
      _ <= ENNReal.ofReal delta := hbase.2

end OFUL
end BanditRLProof
