import BanditRLProof.Exp3BestArm
import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityAllHorizon

/-!
# Best-arm all-horizon pathwise-variance EXP3

This module upgrades the fixed supported-comparator all-horizon tail to the
best supported arm in hindsight. The confidence budget is calibrated armwise
as `delta / K`. The fixed-comparator off-sparsityFailure tail is unioned over
the arms, so the common sparsity-failure event is added only once afterward.
The strengthened residual is `delta + mu(sparsityFailure)`, and its practical
consumer needs only `mu(sparsityFailure) <= ofReal epsilon`.

The older `delta + K * mu(sparsityFailure)` and `epsilon / K` wrappers remain
available as compatibility APIs.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Best-arm all-horizon threshold. The fixed-comparator schedule receives
the armwise confidence share `delta / K`. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon sparsity : Nat)
    (delta : Real) : Real :=
  pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold
    arms horizon sparsity (delta / (arms.card : Real))

/-- Best-arm all-horizon tail away from the common support-sparsity failure
event. The comparator union spends only the armwise confidence shares. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail_off_sparsityFailure
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
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
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
  let eta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity deltaArm
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma
      (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two)
        (by exact_mod_cast hsparsity)
        (by exact_mod_cast hhorizon)).le
      (by
        exact
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
            (arms.card : Real) (sparsity : Real) (horizon : Real)
              deltaArm).trans (by norm_num))
      loss.environment
  let threshold :=
    pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
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
      sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity deltaArm hdeltaArm_pos hdeltaArm_le_one
    dsimp only at h
    simpa [
      mu, armBad, threshold, realizedLoss, comparatorLoss, sparsityBad,
      pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold,
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

/-- All-horizon best-arm residual theorem. The common sparsity-failure event
is charged once for every arm because this wrapper consumes only the compiled
fixed-comparator residual surface. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} <=
      ENNReal.ofReal delta +
        (arms.card : ENNReal) *
          mu (sampledPredictableSparsityFailure
            arms loss horizon sparsity) := by
  dsimp only
  classical
  let deltaArm : Real := delta / (arms.card : Real)
  let gamma :=
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
  let eta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity deltaArm
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma
      (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two)
        (by exact_mod_cast hsparsity)
        (by exact_mod_cast hhorizon)).le
      (by
        exact
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
            (arms.card : Real) (sparsity : Real) (horizon : Real)
              deltaArm).trans (by norm_num))
      loss.environment
  let threshold :=
    pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
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
  have hdeltaArm_pos : 0 < deltaArm := by
    exact div_pos hdelta hcardReal_pos
  have hdelta_le_card : delta <= (arms.card : Real) := by
    have hcardReal_one : (1 : Real) <= (arms.card : Real) := by
      exact_mod_cast (show 1 <= arms.card by omega)
    exact hdelta_le_one.trans hcardReal_one
  have hdeltaArm_le_one : deltaArm <= 1 := by
    exact (div_le_one hcardReal_pos).2 hdelta_le_card
  have htail :
      ∀ comparator ∈ arms,
        mu (armBad comparator) <=
          ENNReal.ofReal deltaArm + mu sparsityBad := by
    intro comparator hcomparator
    have h :=
      sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity deltaArm hdeltaArm_pos hdeltaArm_le_one
    dsimp only at h
    simpa [
      mu, armBad, threshold, realizedLoss, comparatorLoss, sparsityBad,
      pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold,
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
  have hcardENN_ne_zero : (arms.card : ENNReal) ≠ 0 := by
    simp [Finset.card_ne_zero.mpr harms]
  have hcardENN_ne_top : (arms.card : ENNReal) ≠ ⊤ := by simp
  change
    mu {sample |
        threshold <=
          realizedLoss sample -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} <=
      ENNReal.ofReal delta + (arms.card : ENNReal) * mu sparsityBad
  rw [hevent]
  calc
    mu (⋃ comparator ∈ arms, armBad comparator) <=
        ∑ comparator ∈ arms, mu (armBad comparator) :=
      measure_biUnion_finset_le arms armBad
    _ <=
        ∑ _comparator ∈ arms,
          (ENNReal.ofReal deltaArm + mu sparsityBad) := by
      exact Finset.sum_le_sum fun comparator hcomparator =>
        htail comparator hcomparator
    _ = (arms.card : ENNReal) *
          (ENNReal.ofReal deltaArm + mu sparsityBad) := by
      simp [nsmul_eq_mul, mul_add]
    _ = ENNReal.ofReal delta +
          (arms.card : ENNReal) * mu sparsityBad := by
      rw [mul_add]
      congr 1
      dsimp [deltaArm]
      rw [ENNReal.ofReal_div_of_pos hcardReal_pos]
      simp only [ENNReal.ofReal_natCast]
      exact ENNReal.mul_div_cancel hcardENN_ne_zero hcardENN_ne_top

/-- Practical best-arm all-horizon theorem. Per-arm calibration of both
confidence and sparsity-failure budgets yields total failure
`delta + epsilon`. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail_of_sparsityFailure_le
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal (epsilon / (arms.card : Real)) →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
              arms horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              sampledPredictableBestArmCumulativeLoss
                arms harms loss horizon sample} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
        delta hdelta hdelta_le_one
  dsimp only at htail
  have hcardReal_pos : 0 < (arms.card : Real) := by
    exact_mod_cast Finset.card_pos.mpr harms
  have hcardENN_ne_zero : (arms.card : ENNReal) ≠ 0 := by
    simp [Finset.card_ne_zero.mpr harms]
  have hcardENN_ne_top : (arms.card : ENNReal) ≠ ⊤ := by simp
  have hscaled :
      (arms.card : ENNReal) *
          (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
            (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
              arms
                (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
                  (arms.card : Real) (sparsity : Real) (horizon : Real)
                    (delta / (arms.card : Real)))
                horizon sparsity (delta / (arms.card : Real)))
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                (delta / (arms.card : Real)))
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                (delta / (arms.card : Real))
              (by exact_mod_cast hcard_two)
              (by exact_mod_cast hsparsity)
              (by exact_mod_cast hhorizon)).le
            (by
              exact
                (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
                  (arms.card : Real) (sparsity : Real) (horizon : Real)
                    (delta / (arms.card : Real))).trans (by norm_num))
            loss.environment)
            (sampledPredictableSparsityFailure
              arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon := by
    calc
      _ <= (arms.card : ENNReal) *
          ENNReal.ofReal (epsilon / (arms.card : Real)) :=
        mul_le_mul_right hfailure _
      _ = ENNReal.ofReal epsilon := by
        rw [ENNReal.ofReal_div_of_pos hcardReal_pos]
        simp only [ENNReal.ofReal_natCast]
        exact ENNReal.mul_div_cancel hcardENN_ne_zero hcardENN_ne_top
  exact htail.trans (add_le_add le_rfl hscaled)

/-- All-horizon best-arm residual theorem that charges the common
support-sparsity failure event exactly once. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail_single_sparsityFailure
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
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
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
  let eta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity deltaArm
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma
      (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two)
        (by exact_mod_cast hsparsity)
        (by exact_mod_cast hhorizon)).le
      (by
        exact
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
            (arms.card : Real) (sparsity : Real) (horizon : Real)
              deltaArm).trans (by norm_num))
      loss.environment
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
          arms horizon sparsity delta <=
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          sampledPredictableBestArmCumulativeLoss
            arms harms loss horizon sample}
  have hoff :=
    sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail_off_sparsityFailure
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

/-- Practical best-arm all-horizon theorem with a single charge for the
common support-sparsity failure event. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail_of_sparsityFailure_le_single_charge
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                deltaArm).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
              arms horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              sampledPredictableBestArmCumulativeLoss
                arms harms loss horizon sample} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceBestArmRealizedRegret_tail_single_sparsityFailure
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
        delta hdelta hdelta_le_one
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
