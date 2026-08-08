import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityBestArmAllHorizon

/-!
# Eventual refined best-arm sparse EXP3 tail

For fixed model parameters, the four deterministic large-horizon inequalities
used by the exact double-predictable-variance sparse EXP3 schedule eventually
hold automatically. This module therefore removes the coarse `T + 1` fallback
eventually, identifies the best-arm threshold with `16 * gamma_T * T`, and
reuses the existing off-sparsity, residual, and practical tails under the same
horizon-indexed generated trajectory measures.
-/

namespace BanditRLProof.Exp3

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open scoped Topology

private theorem eventually_const_le_natCast (c : Real) :
    ∀ᶠ n : Nat in atTop, c <= (n : Real) := by
  obtain ⟨N, hN⟩ := exists_nat_ge c
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.trans (by exact_mod_cast hn)

private theorem eventually_const_le_natCast_pow_three (c : Real) :
    ∀ᶠ n : Nat in atTop, c <= (n : Real) ^ 3 := by
  obtain ⟨N, hN⟩ := exists_nat_ge c
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hNn : N <= n := (Nat.le_max_left N 1).trans hn
  have h1n : 1 <= n := (Nat.le_max_right N 1).trans hn
  have hcast : c <= (n : Real) := hN.trans (by exact_mod_cast hNn)
  have hn0 : 0 <= (n : Real) := by positivity
  have hn1 : (1 : Real) <= n := by exact_mod_cast h1n
  have hone_le_sq : (1 : Real) <= (n : Real) * n := by nlinarith
  calc
    c <= (n : Real) := hcast
    _ = (n : Real) * 1 := by ring
    _ <= (n : Real) * ((n : Real) * n) :=
      mul_le_mul_of_nonneg_left hone_le_sq hn0
    _ = (n : Real) ^ 3 := by ring

/-- Every fixed choice of the four real-valued scale parameters eventually
satisfies the deterministic large-horizon inequalities. -/
theorem eventually_doubleVarianceProbabilisticSparseLossLargeHorizonCondition
    (K S delta : Real) :
    ∀ᶠ horizon : Nat in atTop,
      doubleVarianceProbabilisticSparseLossLargeHorizonCondition
        K S (horizon : Real) delta := by
  filter_upwards [
    eventually_const_le_natCast (4 * (S * Real.log K)),
    eventually_const_le_natCast_pow_three
      (32 * (K * S * Real.log K ^ 2 * Real.log (4 / delta))),
    eventually_const_le_natCast (8 * (K * Real.log (4 / delta))),
    eventually_const_le_natCast (4 * (S * Real.log (4 / delta)))]
      with horizon hbase hmixed hconfidence hrealized
  exact ⟨hbase, hmixed, hconfidence, hrealized⟩

/-- On the large-horizon branch, the best-arm all-horizon threshold is exactly
the existing explicit double-variance threshold `16 * gamma * horizon`. -/
theorem
    doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold_eq_explicit_of_largeHorizon
    {Action : Type*} (arms : Finset Action) (horizon sparsity : Nat)
    (delta : Real)
    (hlarge :
      doubleVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real)
          (delta / (arms.card : Real))) :
    doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
        arms horizon sparsity delta =
      pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
        arms
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real)
              (delta / (arms.card : Real)))
          horizon sparsity (delta / (arms.card : Real)) := by
  simp [
    doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold,
    doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
    hlarge]

/-- Pointwise off-sparsity tail with the explicit threshold, obtained without
changing the generated trajectory measure selected by the parent theorem. -/
theorem
    sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_off_sparsityFailure_of_largeHorizon
    {Env Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : MeasureTheory.Measure Env) [MeasureTheory.IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge :
      doubleVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real)
          (delta / (arms.card : Real))) :
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
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
            arms gamma horizon sparsity deltaArm <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal delta := by
  dsimp only
  have htail :=
    sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
        delta hdelta hdelta_le_one
  dsimp only at htail
  rw [
    doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold_eq_explicit_of_largeHorizon
      arms horizon sparsity delta hlarge] at htail
  exact htail

/-- Pointwise residual tail with the explicit threshold. The sparsity-failure
term is retained exactly as in the all-horizon parent theorem. -/
theorem
    sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_largeHorizon
    {Env Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge :
      doubleVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real)
          (delta / (arms.card : Real))) :
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
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
            arms gamma horizon sparsity deltaArm <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} <=
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure
          arms loss horizon sparsity) := by
  dsimp only
  have htail :=
    sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
        delta hdelta hdelta_le_one
  dsimp only at htail
  rw [
    doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold_eq_explicit_of_largeHorizon
      arms horizon sparsity delta hlarge] at htail
  exact htail

/-- Pointwise practical tail after supplying an outer-measure bound for the
sparsity-failure event. -/
theorem
    sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le_of_largeHorizon
    {Env Action : Type*}
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
    (hdelta_le_one : delta <= 1)
    (hlarge :
      doubleVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real)
          (delta / (arms.card : Real))) :
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
        ENNReal.ofReal epsilon ->
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
              arms gamma horizon sparsity deltaArm <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              sampledPredictableBestArmCumulativeLoss
                arms harms loss horizon sample} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
        delta epsilon hdelta hdelta_le_one
  dsimp only at htail
  have htail' := htail hfailure
  rw [
    doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold_eq_explicit_of_largeHorizon
      arms horizon sparsity delta hlarge] at htail'
  exact htail'

/-- Eventually, every positive horizon has the explicit off-sparsity tail.
Each horizon retains its own internally selected rates and trajectory measure. -/
theorem
    eventually_sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_off_sparsityFailure
    {Env Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (sparsity : Nat) (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    ∀ᶠ horizon : Nat in atTop,
      0 < horizon ∧
        ∀ hhorizon : 0 < horizon,
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
              pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
                  arms gamma horizon sparsity deltaArm <=
                (Finset.range horizon).sum (fun t =>
                    sampledTrajectoryRealizedLossAt t sample) -
                  sampledPredictableBestArmCumulativeLoss
                    arms harms loss horizon sample} \
            sampledPredictableSparsityFailure arms loss horizon sparsity) <=
              ENNReal.ofReal delta := by
  let deltaArm := delta / (arms.card : Real)
  filter_upwards [
    eventually_ge_atTop 1,
    eventually_doubleVarianceProbabilisticSparseLossLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) deltaArm]
      with horizon hhorizon hlarge
  have hhorizon_pos : 0 < horizon := by omega
  refine ⟨hhorizon_pos, ?_⟩
  intro hhorizon'
  exact
    sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_off_sparsityFailure_of_largeHorizon
      prior arms harms hcard_two loss horizon sparsity hhorizon' hsparsity
        delta hdelta hdelta_le_one hlarge

/-- Eventually, every positive horizon has the explicit residual tail. This is
an at-top statement about horizon-indexed measures, not an anytime event. -/
theorem
    eventually_sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail
    {Env Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (sparsity : Nat) (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    ∀ᶠ horizon : Nat in atTop,
      0 < horizon ∧
        ∀ hhorizon : 0 < horizon,
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
              pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
                  arms gamma horizon sparsity deltaArm <=
                (Finset.range horizon).sum (fun t =>
                    sampledTrajectoryRealizedLossAt t sample) -
                  sampledPredictableBestArmCumulativeLoss
                    arms harms loss horizon sample} <=
            ENNReal.ofReal delta +
              mu (sampledPredictableSparsityFailure
                arms loss horizon sparsity) := by
  let deltaArm := delta / (arms.card : Real)
  filter_upwards [
    eventually_ge_atTop 1,
    eventually_doubleVarianceProbabilisticSparseLossLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) deltaArm]
      with horizon hhorizon hlarge
  have hhorizon_pos : 0 < horizon := by omega
  refine ⟨hhorizon_pos, ?_⟩
  intro hhorizon'
  exact
    sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_largeHorizon
      prior arms harms hcard_two loss horizon sparsity hhorizon' hsparsity
        delta hdelta hdelta_le_one hlarge

/-- Eventually, an external sparsity-failure bound yields the explicit
practical tail under the same horizon-indexed generated trajectory measures. -/
theorem
    eventually_sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le
    {Env Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (sparsity : Nat) (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) :
    ∀ᶠ horizon : Nat in atTop,
      0 < horizon ∧
        ∀ hhorizon : 0 < horizon,
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
              ENNReal.ofReal epsilon ->
            mu {sample |
                pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
                    arms gamma horizon sparsity deltaArm <=
                  (Finset.range horizon).sum (fun t =>
                      sampledTrajectoryRealizedLossAt t sample) -
                    sampledPredictableBestArmCumulativeLoss
                      arms harms loss horizon sample} <=
              ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  let deltaArm := delta / (arms.card : Real)
  filter_upwards [
    eventually_ge_atTop 1,
    eventually_doubleVarianceProbabilisticSparseLossLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) deltaArm]
      with horizon hhorizon hlarge
  have hhorizon_pos : 0 < horizon := by omega
  refine ⟨hhorizon_pos, ?_⟩
  intro hhorizon'
  exact
    sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le_of_largeHorizon
      prior arms harms hcard_two loss horizon sparsity hhorizon' hsparsity
        delta epsilon hdelta hdelta_le_one hlarge

end BanditRLProof.Exp3
