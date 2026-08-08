import BanditRLProof.OFULScheduledBlockStartForcedAllTimeConfidence

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set

namespace BanditRLProof
namespace OFUL

/-- History indices whose successor action is prescribed by the block-start schedule. -/
def blockStartForcedIndexSet (window horizon : Nat) : Finset Nat :=
  (Finset.range horizon).filter (fun n => n % window = 0)

/--
Every forced index below `horizon` belongs to the image of the quotient-block
range under `block ↦ block * window`, so its cardinality is at most the number
of quotient blocks. With `window = 0`, the modulo condition reduces to `n = 0`,
and the same conservative bound remains valid.
-/
theorem card_blockStartForcedIndexSet_le_div_add_one
    (window horizon : Nat) :
    (blockStartForcedIndexSet window horizon).card <=
      horizon / window + 1 := by
  let quotientMultiples :=
    (Finset.range (horizon / window + 1)).image (fun block => block * window)
  have hsubset :
      blockStartForcedIndexSet window horizon ⊆ quotientMultiples := by
    intro n hn
    have hn_filter := Finset.mem_filter.mp hn
    have hn_lt : n < horizon := Finset.mem_range.mp hn_filter.1
    have hn_mod : n % window = 0 := hn_filter.2
    apply Finset.mem_image.mpr
    refine ⟨n / window, Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hn_lt))
    · exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hn_mod)
  calc
    (blockStartForcedIndexSet window horizon).card <=
        quotientMultiples.card :=
      Finset.card_le_card hsubset
    _ <= (Finset.range (horizon / window + 1)).card := by
      exact Finset.card_image_le
    _ = horizon / window + 1 := Finset.card_range _

/-- A pointwise forced-arm gap ceiling bounds the forced charge by its cardinality. -/
theorem blockStartForcedActionSuccessorPseudoRegret_le_card_mul
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    (window horizon : Nat)
    (forcedGapBound : Real)
    (hforcedGap : forall block,
      linearValue thetaStar (actionFeature best) -
          linearValue thetaStar (actionFeature (forcedAction block)) <=
        forcedGapBound) :
    blockStartForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction window horizon <=
      ((blockStartForcedIndexSet window horizon).card : Real) *
        forcedGapBound := by
  have hsum :=
    Finset.sum_le_card_nsmul
      (blockStartForcedIndexSet window horizon)
      (fun n =>
        linearValue thetaStar (actionFeature best) -
          linearValue thetaStar (actionFeature (forcedAction (n / window))))
      forcedGapBound
      (fun n _hn => hforcedGap (n / window))
  simpa only [
    blockStartForcedActionSuccessorPseudoRegret,
    blockStartForcedIndexSet,
    nsmul_eq_mul,
    Nat.cast_ofNat] using hsum

/-- The forced charge is at most the number of quotient blocks times a gap ceiling. -/
theorem blockStartForcedActionSuccessorPseudoRegret_le_div_add_one_mul
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    (window horizon : Nat)
    (forcedGapBound : Real)
    (hforcedGapBound : 0 <= forcedGapBound)
    (hforcedGap : forall block,
      linearValue thetaStar (actionFeature best) -
          linearValue thetaStar (actionFeature (forcedAction block)) <=
        forcedGapBound) :
    blockStartForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction window horizon <=
      ((horizon / window + 1 : Nat) : Real) * forcedGapBound := by
  calc
    blockStartForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction window horizon <=
      ((blockStartForcedIndexSet window horizon).card : Real) *
        forcedGapBound :=
      blockStartForcedActionSuccessorPseudoRegret_le_card_mul
        thetaStar actionFeature best forcedAction window horizon
        forcedGapBound hforcedGap
    _ <= ((horizon / window + 1 : Nat) : Real) * forcedGapBound := by
      apply mul_le_mul_of_nonneg_right _ hforcedGapBound
      exact_mod_cast card_blockStartForcedIndexSet_le_div_add_one window horizon

/--
Linear parameter and arm envelopes instantiate the generic forced-gap ceiling.
No separate `0 <= L2` hypothesis is needed here: `Real.sqrt L2` is nonnegative,
and the arm bound at `best` already rules out a negative feasible `L2`.
-/
theorem
    blockStartForcedActionSuccessorPseudoRegret_le_div_add_one_mul_two_mul_parameterFeatureBound
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
    (window horizon : Nat) :
    blockStartForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction window horizon <=
      ((horizon / window + 1 : Nat) : Real) *
        (2 * S * Real.sqrt L2) := by
  apply
    blockStartForcedActionSuccessorPseudoRegret_le_div_add_one_mul
      thetaStar actionFeature best forcedAction window horizon
      (2 * S * Real.sqrt L2)
  · positivity
  · intro block
    exact
      linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
        thetaStar (actionFeature best) (actionFeature (forcedAction block))
        S L2 hS htheta
        (hactionFeatureBound best)
        (hactionFeatureBound (forcedAction block))

/-- Fully scalar all-horizon violation event for the block-start forced policy. -/
noncomputable def
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (window : Nat)
    (best : Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory | exists horizon,
    ((horizon / window + 1 : Nat) : Real) *
          (2 * S * Real.sqrt L2) +
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2 <
      canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory}

/-- The scalar-budget violation event is contained in the forced-charge event. -/
theorem
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet_subset
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
    (window : Nat)
    (best : Fin K) :
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2
        window best ⊆
      blockStartForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2
        forcedAction window best := by
  intro trajectory htrajectory
  rcases htrajectory with ⟨horizon, hviolation⟩
  refine ⟨horizon, ?_⟩
  exact lt_of_le_of_lt
    (by
      have hcharge :=
        blockStartForcedActionSuccessorPseudoRegret_le_div_add_one_mul_two_mul_parameterFeatureBound
          thetaStar actionFeature S L2 hS htheta hactionFeatureBound
          best forcedAction window horizon
      linarith)
    hviolation

/--
Complete all-horizon theorem with the forced-action charge replaced by the
scalar quotient-block count and the common linear arm-gap envelope.
-/
theorem
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_scalarAllHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (window : Nat)
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
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2
            window best) <=
        ENNReal.ofReal delta := by
  have hbase :=
    blockStartForcedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS forcedAction window environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
  constructor
  · exact hbase.1
  · calc
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2
            window best) <=
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2
            forcedAction window best) := by
        exact measure_mono
          (blockStartForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet_subset
            lambda thetaStar actionFeature R delta S L2 hS
            source.theta_norm_le hactionFeatureBound forcedAction window best)
      _ <= ENNReal.ofReal delta := hbase.2

end OFUL
end BanditRLProof
