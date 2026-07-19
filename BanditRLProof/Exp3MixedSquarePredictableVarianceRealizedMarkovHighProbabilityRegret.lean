import BanditRLProof.Exp3MixedSquarePredictableVarianceRealizedHighProbabilityRegret
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Realized EXP3 regret from a predictable-variance expectation budget

This module discharges the explicit predictable-variance overflow residual by
Markov's inequality. The resulting theorem requires a caller-supplied
`lintegral` bound for the cumulative predictable mixed-square variance; no
such algorithm-specific expectation bound is inferred from predictability.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Cumulative predictable mixed-square variance on a generated trajectory. -/
noncomputable def sampledPredictableMixedSquaredVarianceSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    Env × ((k : Nat) → Action × Real) → Real :=
  fun sample => (Finset.range horizon).sum (fun i =>
    sampledTrajectoryPredictableMixedSquaredVarianceAt
      arms eta gamma loss i sample)

theorem measurable_sampledPredictableMixedSquaredVarianceSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    Measurable (sampledPredictableMixedSquaredVarianceSum
      arms eta gamma loss horizon) := by
  refine Finset.measurable_sum (Finset.range horizon) fun i _hi => ?_
  exact measurable_sampledTrajectoryPredictableMixedSquaredVarianceAt
    arms harms eta gamma hgamma_pos hgamma_le_one loss i

theorem sampledPredictableMixedSquaredVarianceSum_nonneg
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    0 ≤ sampledPredictableMixedSquaredVarianceSum
      arms eta gamma loss horizon sample := by
  exact Finset.sum_nonneg fun i _hi =>
    sampledTrajectoryPredictableMixedSquaredVarianceAt_nonneg
      arms harms eta gamma hgamma_nonneg hgamma_le_one loss i sample

/-- `lintegral` form of the cumulative predictable mixed-square variance. -/
noncomputable def sampledPredictableMixedSquaredVarianceLIntegral
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real)))
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (horizon : Nat) : ENNReal :=
  ∫⁻ sample, ENNReal.ofReal
    (sampledPredictableMixedSquaredVarianceSum
      arms eta gamma loss horizon sample) ∂mu

/-- Mathlib-backed Markov tail for cumulative predictable mixed-square
variance. The measure need not be finite. -/
theorem measure_sampledPredictableMixedSquaredVarianceSum_gt_le_lintegral_div
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real)))
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (varianceBudget : Real) (hvarianceBudget : 0 < varianceBudget) :
    mu {sample |
        varianceBudget < sampledPredictableMixedSquaredVarianceSum
          arms eta gamma loss horizon sample} ≤
      sampledPredictableMixedSquaredVarianceLIntegral
          mu arms eta gamma loss horizon /
        ENNReal.ofReal varianceBudget := by
  let varianceSum := sampledPredictableMixedSquaredVarianceSum
    arms eta gamma loss horizon
  have hvarianceSum : Measurable varianceSum :=
    measurable_sampledPredictableMixedSquaredVarianceSum
      arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
  have hofReal : AEMeasurable (fun sample =>
      ENNReal.ofReal (varianceSum sample)) mu :=
    (ENNReal.measurable_ofReal.comp hvarianceSum).aemeasurable
  have hmarkov := meas_ge_le_lintegral_div hofReal
    (ENNReal.ofReal_pos.2 hvarianceBudget).ne'
    ENNReal.ofReal_ne_top
  calc
    mu {sample | varianceBudget < varianceSum sample} ≤
        mu {sample |
          ENNReal.ofReal varianceBudget ≤ ENNReal.ofReal (varianceSum sample)} := by
      apply measure_mono
      intro sample hsample
      exact ENNReal.ofReal_le_ofReal hsample.le
    _ ≤ (∫⁻ sample, ENNReal.ofReal (varianceSum sample) ∂mu) /
          ENNReal.ofReal varianceBudget := hmarkov
    _ = sampledPredictableMixedSquaredVarianceLIntegral
          mu arms eta gamma loss horizon /
        ENNReal.ofReal varianceBudget := by
      rfl

/-- Consume a cumulative predictable-variance `lintegral` budget in the
realized-regret residual theorem. -/
theorem sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_of_lintegral_variance_le
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (varianceBudget deltaSquare deltaConfidence deltaRealized : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized)
    (varianceMeanBudget : Real)
    (hvarianceLIntegral :
      sampledPredictableMixedSquaredVarianceLIntegral
          (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
            eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
          arms eta gamma loss horizon ≤ ENNReal.ofReal varianceMeanBudget) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
            arms eta gamma horizon varianceBudget deltaSquare deltaConfidence
              deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      (((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized) +
        ENNReal.ofReal varianceMeanBudget /
          ENNReal.ofReal varianceBudget := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  have hregret :=
    sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon varianceBudget deltaSquare deltaConfidence
        deltaRealized hvarianceBudget hdeltaSquare hdeltaConfidence hdeltaRealized
  dsimp only at hregret
  have hoverflow :=
    measure_sampledPredictableMixedSquaredVarianceSum_gt_le_lintegral_div
      mu arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
        varianceBudget hvarianceBudget
  have hoverflow' :
      mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} ≤
        ENNReal.ofReal varianceMeanBudget /
          ENNReal.ofReal varianceBudget := by
    calc
      mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} ≤
          sampledPredictableMixedSquaredVarianceLIntegral
              mu arms eta gamma loss horizon /
            ENNReal.ofReal varianceBudget := by
        simpa [sampledPredictableMixedSquaredVarianceSum] using hoverflow
      _ ≤ ENNReal.ofReal varianceMeanBudget /
          ENNReal.ofReal varianceBudget :=
        ENNReal.div_le_div hvarianceLIntegral le_rfl
  exact hregret.trans (add_le_add_right hoverflow' _)

/-- Five-event realized-regret budget: four confidence failures and one
Markov predictable-variance overflow failure. -/
noncomputable def sampledPredictableVarianceSquareRealizedMarkovHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (varianceMeanBudget delta : Real) : Real :=
  sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
    arms eta gamma horizon (varianceMeanBudget / (delta / 5))
      (delta / 5) (delta / 5) (delta / 5)

/-- Primary Markov-closed realized-regret theorem. A cumulative predictable
variance `lintegral` bound is allocated the fifth failure probability. -/
theorem sampledPredictable_predictableVarianceSquareRealizedMarkovHighProbabilityRegret_tail_total_delta
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (varianceMeanBudget delta : Real)
    (hvarianceMeanBudget : 0 < varianceMeanBudget) (hdelta : 0 < delta)
    (hvarianceLIntegral :
      sampledPredictableMixedSquaredVarianceLIntegral
          (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
            eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
          arms eta gamma loss horizon ≤ ENNReal.ofReal varianceMeanBudget) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareRealizedMarkovHighProbabilityRegretBudget
            arms eta gamma horizon varianceMeanBudget delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta := by
  have hfifth_pos : 0 < delta / 5 := div_pos hdelta (by norm_num)
  have hvarianceBudget : 0 < varianceMeanBudget / (delta / 5) :=
    div_pos hvarianceMeanBudget hfifth_pos
  have h :=
    sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_of_lintegral_variance_le
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon (varianceMeanBudget / (delta / 5))
        (delta / 5) (delta / 5) (delta / 5) hvarianceBudget hfifth_pos
        hfifth_pos hfifth_pos varianceMeanBudget hvarianceLIntegral
  dsimp only at h ⊢
  have hmean_ne_zero : ENNReal.ofReal varianceMeanBudget ≠ 0 :=
    (ENNReal.ofReal_pos.2 hvarianceMeanBudget).ne'
  have hratio :
      ENNReal.ofReal varianceMeanBudget /
          ENNReal.ofReal (varianceMeanBudget / (delta / 5)) =
        ENNReal.ofReal (delta / 5) := by
    rw [ENNReal.ofReal_div_of_pos hfifth_pos]
    exact ENNReal.div_div_cancel hmean_ne_zero ENNReal.ofReal_ne_top
  have hfifth_nonneg : 0 ≤ delta / 5 := hfifth_pos.le
  have hprob :
      (((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
          ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5)) +
          ENNReal.ofReal (delta / 5) = ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hfifth_nonneg hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hfifth_nonneg hfifth_nonneg) hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hfifth_nonneg hfifth_nonneg)
        hfifth_nonneg) hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg
        (add_nonneg (add_nonneg hfifth_nonneg hfifth_nonneg)
          hfifth_nonneg) hfifth_nonneg) hfifth_nonneg]
    congr 1
    ring
  rw [hratio, hprob] at h
  simpa [sampledPredictableVarianceSquareRealizedMarkovHighProbabilityRegretBudget]
    using h

end BanditRLProof.Exp3
