import BanditRLProof.Exp3SampledHedge

/-!
# Almost-sure Hedge control for predictable sampled EXP3

This module discharges the pathwise nonnegative-feedback premise of
`Exp3SampledHedge` from the generated predictable `[0,1]` reward law.  It first
aggregates the time-zero and successor reward identifications into one
finite-horizon almost-sure event, then applies the concrete pathwise Hedge
bound on that event.

The endpoint remains an almost-sure inequality.  Integrating it and comparing
the pure Hedge distribution with the exploration-mixed sampling distribution
are separate downstream steps.
-/

namespace BanditRLProof
namespace Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Every observed scalar reward is nonnegative almost surely under the
generated predictable sampled-EXP3 trajectory law. -/
theorem sampledPredictableTrajectoryMeasure_reward_nonneg_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu, 0 <= (sample.2 t).2 := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  cases t with
  | zero =>
      have hreward :
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.2 0).2) =ᵐ[mu]
          (fun sample => loss.initial sample.1 (sample.2 0).1) := by
        simpa [mu, sampledImportanceWeightedTrajectoryKernel] using
          (canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
            prior (sampledImportanceWeightedHistoryAlgorithm arms harms eta gamma
              hgamma_nonneg hgamma_le_one) loss)
      filter_upwards [hreward] with sample hsample
      rw [hsample]
      exact (loss.initial_mem_unitInterval sample.1 (sample.2 0).1).1
  | succ n =>
      have hreward :
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.2 (n + 1)).2) =ᵐ[mu]
          (fun sample => loss.successor n sample.1
            (Preorder.frestrictLe n sample.2) (sample.2 (n + 1)).1) := by
        simpa [mu] using
          (sampledPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
            prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)
      filter_upwards [hreward] with sample hsample
      rw [hsample]
      exact (loss.successor_mem_unitInterval n sample.1
        (Preorder.frestrictLe n sample.2) (sample.2 (n + 1)).1).1

/-- One common almost-sure event supplies reward nonnegativity at every time
strictly before a finite horizon. -/
theorem sampledPredictableTrajectoryMeasure_finiteHorizon_reward_nonneg_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu, ∀ t, t < horizon -> 0 <= (sample.2 t).2 := by
  dsimp only
  rw [ae_all_iff]
  intro t
  have hnonneg := sampledPredictableTrajectoryMeasure_reward_nonneg_ae
    prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss t
  dsimp only at hnonneg
  filter_upwards [hnonneg] with sample hsample
  intro _ht
  exact hsample

/-- The concrete finite-horizon Hedge inequality holds almost surely on the
generated predictable sampled-EXP3 trajectory. -/
theorem sampledPredictableTrajectoryMeasure_hedge_regret_le_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu,
      (Finset.range horizon).sum (fun t =>
          mixedLoss arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t) -
          cumulativeLoss (sampledTrajectoryObservedLoss arms eta gamma sample)
            horizon comparator <=
        Real.log arms.card / eta +
          eta * (Finset.range horizon).sum (fun t =>
            mixedSquaredLoss arms eta
              (sampledTrajectoryObservedLoss arms eta gamma sample) t) := by
  dsimp only
  have hnonneg :=
    sampledPredictableTrajectoryMeasure_finiteHorizon_reward_nonneg_ae
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss horizon
  dsimp only at hnonneg
  filter_upwards [hnonneg] with sample hsample
  exact sampledTrajectory_hedge_regret_le arms harms eta gamma heta
    hgamma_nonneg hgamma_le_one sample horizon hsample comparator hcomparator

/-- The same almost-sure inequality with the comparator cumulative estimator
exposed as the inclusive concrete sampled history score. -/
theorem sampledPredictableScoreHedge_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu,
      (Finset.range (n + 1)).sum (fun t =>
          mixedLoss arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t) -
          sampledHistoryScore arms eta gamma n
            (Preorder.frestrictLe n sample.2) comparator <=
        Real.log arms.card / eta +
          eta * (Finset.range (n + 1)).sum (fun t =>
            mixedSquaredLoss arms eta
              (sampledTrajectoryObservedLoss arms eta gamma sample) t) := by
  dsimp only
  have hnonneg :=
    sampledPredictableTrajectoryMeasure_finiteHorizon_reward_nonneg_ae
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss (n + 1)
  dsimp only at hnonneg
  filter_upwards [hnonneg] with sample hsample
  exact sampledHistoryScore_hedge_regret_le arms harms eta gamma heta
    hgamma_nonneg hgamma_le_one sample n hsample comparator hcomparator

end Exp3
end BanditRLProof
