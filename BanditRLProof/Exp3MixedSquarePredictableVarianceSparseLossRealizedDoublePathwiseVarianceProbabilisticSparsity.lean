import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsity
import BanditRLProof.Exp3MixedSquarePredictableVarianceSmallLossRealizedDoublePredictableVarianceHighProbabilityRegret

/-!
# Sparse realized EXP3 regret with two pathwise variance budgets

Outside the explicit sparsity-failure event, the mixed-square predictable
variance is bounded by `(1 / (gamma / K)) * (S * T)` and the exact
selected-loss predictable variance is bounded by `S * T`. Four confidence
events receive `delta / 4`, and the common sparsity-failure set is charged
exactly once.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

noncomputable def sampledPredictableSparseRealizedVarianceBudget
    (horizon sparsity : Nat) : Real :=
  (sparsity : Real) * (horizon : Real)

theorem sampledPredictableRealizedVarianceSum_le_sparseRealizedVarianceBudget_or_mem_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss i sample) ≤
        sampledPredictableSparseRealizedVarianceBudget horizon sparsity ∨
      sample ∈ sampledPredictableSparsityFailure
        arms loss horizon sparsity := by
  rcases sampledPredictableLossMassSum_le_or_mem_sparsityFailure
      arms loss horizon sparsity sample with hmass | hbad
  · left
    exact
      (sampledPredictableRealizedVariance_sum_le_lossMass
        arms harms eta gamma hgamma_nonneg hgamma_le_one loss horizon
          sample).trans
        (by simpa [sampledPredictableLossMassSum,
          sampledPredictableSparseRealizedVarianceBudget] using hmass)
  · exact Or.inr hbad

noncomputable def sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon sparsity : Nat)
    (delta : Real) : Real :=
  sampledPredictableVarianceSquareSmallLossDoubleVarianceRealizedHighProbabilityRegretBudget
    arms eta gamma horizon
      ((sparsity : Real) * (horizon : Real))
      (sampledPredictableSparsePathwiseVarianceBudget
        arms gamma horizon sparsity)
      (sampledPredictableSparseRealizedVarianceBudget horizon sparsity)
      (delta / 4) (delta / 4) (delta / 4)

theorem sampledPredictable_doubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegret_tail_off_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu ({sample |
        sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal delta := by
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let lossMassBudget := (sparsity : Real) * (horizon : Real)
  let mixedVarianceBudget :=
    sampledPredictableSparsePathwiseVarianceBudget
      arms gamma horizon sparsity
  let realizedVarianceBudget :=
    sampledPredictableSparseRealizedVarianceBudget horizon sparsity
  let regretBudget :=
    sampledPredictableVarianceSquareSmallLossDoubleVarianceRealizedHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget mixedVarianceBudget
        realizedVarianceBudget (delta / 4) (delta / 4) (delta / 4)
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let regretBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      regretBudget ≤
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  let mixedVarianceSum :=
    fun sample : Env × ((k : Nat) → Action × Real) =>
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample)
  let realizedVarianceSum :=
    fun sample : Env × ((k : Nat) → Action × Real) =>
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss i sample)
  let mixedVarianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | mixedVarianceSum sample ≤ mixedVarianceBudget}
  let realizedVarianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | realizedVarianceSum sample ≤ realizedVarianceBudget}
  have hquarter_pos : 0 < delta / 4 := div_pos hdelta (by norm_num)
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  have hrealizedVarianceBudget : 0 < realizedVarianceBudget := by
    dsimp [realizedVarianceBudget,
      sampledPredictableSparseRealizedVarianceBudget]
    exact mul_pos (Nat.cast_pos.2 hsparsity) (Nat.cast_pos.2 hhorizon)
  have hmixedVarianceBudget : 0 < mixedVarianceBudget := by
    dsimp [mixedVarianceBudget, sampledPredictableSparsePathwiseVarianceBudget]
    exact mul_pos (one_div_pos.2 hfloor_pos) hrealizedVarianceBudget
  have hmass : ∀ᵐ sample ∂mu,
      sampledPredictableLossMassSum arms loss horizon sample ≤
          lossMassBudget ∨
        sample ∈ sparsityBad := by
    exact Filter.Eventually.of_forall fun sample => by
      simpa [lossMassBudget, sparsityBad] using
        sampledPredictableLossMassSum_le_or_mem_sparsityFailure
          arms loss horizon sparsity sample
  have hjoint :
      mu ((regretBad ∩ (mixedVarianceGood ∩ realizedVarianceGood)) \
          sparsityBad) ≤
        (((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
          ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4)) := by
    have h :=
      sampledPredictable_smallLossDoublePredictableVarianceRealizedHighProbabilityRegret_tail_joint_off_bad_of_lossMassSum_le_or_mem
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon lossMassBudget mixedVarianceBudget
          realizedVarianceBudget (delta / 4) (delta / 4) (delta / 4)
          hmixedVarianceBudget hrealizedVarianceBudget
          hquarter_pos hquarter_pos hquarter_pos sparsityBad hmass
    dsimp only at h
    simpa [mu, regretBad, mixedVarianceGood, realizedVarianceGood,
      mixedVarianceSum, realizedVarianceSum, regretBudget] using h
  have hmixedOrBad : ∀ sample,
      mixedVarianceSum sample ≤ mixedVarianceBudget ∨
        sample ∈ sparsityBad := by
    intro sample
    simpa [mixedVarianceSum, mixedVarianceBudget, sparsityBad,
      sampledPredictableMixedSquaredVarianceSum] using
      sampledPredictableMixedSquaredVarianceSum_le_sparsePathwiseVarianceBudget_or_mem_sparsityFailure
        arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon sparsity
          sample
  have hrealizedOrBad : ∀ sample,
      realizedVarianceSum sample ≤ realizedVarianceBudget ∨
        sample ∈ sparsityBad := by
    intro sample
    simpa [realizedVarianceSum, realizedVarianceBudget, sparsityBad] using
      sampledPredictableRealizedVarianceSum_le_sparseRealizedVarianceBudget_or_mem_sparsityFailure
        arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss horizon
          sparsity sample
  have hsplit :
      regretBad \ sparsityBad ⊆
        (regretBad ∩ (mixedVarianceGood ∩ realizedVarianceGood)) \
          sparsityBad := by
    intro sample hsample
    refine ⟨⟨hsample.1, ?_, ?_⟩, hsample.2⟩
    · rcases hmixedOrBad sample with hmixed | hbad
      · exact hmixed
      · exact (hsample.2 hbad).elim
    · rcases hrealizedOrBad sample with hrealized | hbad
      · exact hrealized
      · exact (hsample.2 hbad).elim
  have hquarter_nonneg : 0 ≤ delta / 4 := hquarter_pos.le
  have hprob :
      (((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
          ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4)) =
        ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hquarter_nonneg hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hquarter_nonneg hquarter_nonneg) hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hquarter_nonneg hquarter_nonneg)
        hquarter_nonneg) hquarter_nonneg]
    congr 1
    ring
  have htail : mu (regretBad \ sparsityBad) ≤ ENNReal.ofReal delta := by
    calc
      mu (regretBad \ sparsityBad) ≤
          mu ((regretBad ∩ (mixedVarianceGood ∩ realizedVarianceGood)) \
            sparsityBad) :=
        measure_mono hsplit
      _ ≤ (((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
            ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4)) :=
        hjoint
      _ = ENNReal.ofReal delta := hprob
  simpa [mu, regretBad, regretBudget, lossMassBudget, mixedVarianceBudget,
    realizedVarianceBudget, sparsityBad,
    sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget]
    using htail

theorem sampledPredictable_doubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let regretBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget
          arms eta gamma horizon sparsity delta ≤
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  have hoff :=
    sampledPredictable_doubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegret_tail_off_sparsityFailure
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at hoff
  have hsplit : regretBad ⊆ (regretBad \ sparsityBad) ∪ sparsityBad := by
    intro sample hsample
    by_cases hbad : sample ∈ sparsityBad
    · exact Or.inr hbad
    · exact Or.inl ⟨hsample, hbad⟩
  have htail : mu regretBad ≤ ENNReal.ofReal delta + mu sparsityBad := by
    calc
      mu regretBad ≤ mu ((regretBad \ sparsityBad) ∪ sparsityBad) :=
        measure_mono hsplit
      _ ≤ mu (regretBad \ sparsityBad) + mu sparsityBad :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal delta + mu sparsityBad :=
        add_le_add (by simpa [mu, regretBad, sparsityBad] using hoff) le_rfl
  simpa [mu, regretBad, sparsityBad] using htail

theorem sampledPredictable_doubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegret_tail_of_sparsityFailure_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hfailure :
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
          (sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal epsilon) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  have htail :=
    sampledPredictable_doubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
