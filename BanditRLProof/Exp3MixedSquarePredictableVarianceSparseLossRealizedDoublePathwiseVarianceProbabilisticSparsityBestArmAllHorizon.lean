import BanditRLProof.Exp3BestArm
import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityAllHorizon

/-!
# Best-arm all-horizon sparse EXP3 with two predictable variances

This module upgrades the exact double-variance fixed-comparator all-horizon
tail to the best supported arm in hindsight. Confidence is calibrated at
`delta / K`; the common support-sparsity failure event is removed before the
finite comparator union and added only once afterward.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Best-arm exact double-variance threshold. The fixed-comparator schedule
receives the armwise confidence share `delta / K`. -/
noncomputable def doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon sparsity : Nat)
    (delta : Real) : Real :=
  doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold
    arms horizon sparsity (delta / (arms.card : Real))

/-- Best-arm all-horizon tail away from the common support-sparsity failure
event. The comparator union spends only the armwise confidence shares. -/
theorem sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_off_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let deltaArm := delta / (arms.card : Real)
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu ({sample |
        doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal delta := by
  dsimp only
  classical
  let deltaArm : Real := delta / (arms.card : Real)
  let gamma :=
    doubleVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
  let eta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity deltaArm
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma
      (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two)
        (by exact_mod_cast hsparsity)
        (by exact_mod_cast hhorizon)).le
      (by
        exact
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
            (arms.card : Real) (sparsity : Real) (horizon : Real)
              deltaArm).trans (by norm_num))
      loss.environment
  let threshold :=
    doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
      arms horizon sparsity delta
  let realizedLoss := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum fun t =>
      sampledTrajectoryRealizedLossAt t sample
  let comparatorLoss := fun comparator sample =>
    (Finset.range horizon).sum fun t =>
      predictableLossAt loss t sample comparator
  let armBad := fun comparator =>
    {sample : Env × ((k : Nat) → Action × Real) |
      threshold <= realizedLoss sample - comparatorLoss comparator sample}
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  have hcardReal_pos : 0 < (arms.card : Real) := by
    exact_mod_cast Finset.card_pos.mpr harms
  have hdeltaArm_pos : 0 < deltaArm :=
    div_pos hdelta hcardReal_pos
  have hdelta_le_card : delta <= (arms.card : Real) := by
    have hcardReal_one : (1 : Real) <= (arms.card : Real) := by
      exact_mod_cast (show 1 <= arms.card by omega)
    exact hdelta_le_one.trans hcardReal_one
  have hdeltaArm_le_one : deltaArm <= 1 :=
    (div_le_one hcardReal_pos).2 hdelta_le_card
  have htail :
      ∀ comparator ∈ arms,
        mu (armBad comparator \ sparsityBad) <=
          ENNReal.ofReal deltaArm := by
    intro comparator hcomparator
    have h :=
      sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity deltaArm hdeltaArm_pos hdeltaArm_le_one
    dsimp only at h
    simpa [
      mu, armBad, threshold, realizedLoss, comparatorLoss, sparsityBad,
      doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold,
      deltaArm, gamma, eta] using h
  have hevent :
      {sample : Env × ((k : Nat) → Action × Real) |
          threshold <=
            realizedLoss sample -
              sampledPredictableBestArmCumulativeLoss
                arms harms loss horizon sample} =
        ⋃ comparator ∈ arms, armBad comparator := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    simpa [realizedLoss, comparatorLoss, armBad] using
      (threshold_le_sampledPredictableRealizedLoss_sub_bestArmCumulativeLoss_iff
        arms harms loss horizon sample threshold)
  have hdiff :
      (⋃ comparator ∈ arms, armBad comparator) \ sparsityBad =
        ⋃ comparator ∈ arms, (armBad comparator \ sparsityBad) := by
    ext sample
    simp only [Set.mem_diff, Set.mem_iUnion]
    aesop
  have hcardENN_ne_zero : (arms.card : ENNReal) ≠ 0 := by
    simp [Finset.card_ne_zero.mpr harms]
  have hcardENN_ne_top : (arms.card : ENNReal) ≠ ⊤ := by simp
  change
    mu ({sample |
        threshold <=
          realizedLoss sample -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} \ sparsityBad) <=
      ENNReal.ofReal delta
  rw [hevent, hdiff]
  calc
    mu (⋃ comparator ∈ arms, (armBad comparator \ sparsityBad)) <=
        ∑ comparator ∈ arms, mu (armBad comparator \ sparsityBad) :=
      measure_biUnion_finset_le arms fun comparator =>
        armBad comparator \ sparsityBad
    _ <=
        ∑ _comparator ∈ arms, ENNReal.ofReal deltaArm := by
      exact Finset.sum_le_sum fun comparator hcomparator =>
        htail comparator hcomparator
    _ = (arms.card : ENNReal) * ENNReal.ofReal deltaArm := by
      simp [nsmul_eq_mul]
    _ = ENNReal.ofReal delta := by
      dsimp [deltaArm]
      rw [ENNReal.ofReal_div_of_pos hcardReal_pos]
      simp only [ENNReal.ofReal_natCast]
      exact ENNReal.mul_div_cancel hcardENN_ne_zero hcardENN_ne_top

/-- Best-arm all-horizon residual theorem. The common support-sparsity
failure event is charged exactly once after the comparator union. -/
theorem sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let deltaArm := delta / (arms.card : Real)
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu {sample |
        doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} <=
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure
          arms loss horizon sparsity) := by
  dsimp only
  let deltaArm : Real := delta / (arms.card : Real)
  let gamma :=
    doubleVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
  let eta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity deltaArm
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma
      (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two)
        (by exact_mod_cast hsparsity)
        (by exact_mod_cast hhorizon)).le
      (by
        exact
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
            (arms.card : Real) (sparsity : Real) (horizon : Real)
              deltaArm).trans (by norm_num))
      loss.environment
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
          arms horizon sparsity delta <=
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          sampledPredictableBestArmCumulativeLoss
            arms harms loss horizon sample}
  have hoff :=
    sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
        delta hdelta hdelta_le_one
  dsimp only at hoff
  have hsplit : realizedBad ⊆ (realizedBad \ sparsityBad) ∪ sparsityBad := by
    intro sample hsample
    by_cases hbad : sample ∈ sparsityBad
    · exact Or.inr hbad
    · exact Or.inl ⟨hsample, hbad⟩
  calc
    mu realizedBad <= mu ((realizedBad \ sparsityBad) ∪ sparsityBad) :=
      measure_mono hsplit
    _ <= mu (realizedBad \ sparsityBad) + mu sparsityBad :=
      measure_union_le _ _
    _ <= ENNReal.ofReal delta + mu sparsityBad :=
      add_le_add
        (by
          simpa [mu, realizedBad, sparsityBad, deltaArm, gamma, eta] using
            hoff)
        le_rfl

/-- Practical exact double-variance best-arm theorem with a single charge for
the common support-sparsity failure event. -/
theorem sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) :
    let deltaArm := delta / (arms.card : Real)
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
              arms horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              sampledPredictableBestArmCumulativeLoss
                arms harms loss horizon sample} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
        delta hdelta hdelta_le_one
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
