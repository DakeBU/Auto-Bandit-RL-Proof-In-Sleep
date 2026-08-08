import BanditRLProof.Exp3BernsteinExplicitTuning

/-!
# All-horizon realized EXP3 Bernstein route

The explicit Bernstein schedule gives its `11 * gamma * T` threshold when the
three large-horizon inequalities make clipping inactive. This module closes
the complementary branch honestly: generated realized losses are at most one
almost surely, comparator predictable losses are nonnegative pointwise, and
therefore realized regret is at most `T` almost surely. A branch threshold uses
`T + 1` outside the Bernstein regime, yielding one theorem for every positive
horizon without pretending that the clipped branch satisfies cubic dominance.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Every predictable comparator coordinate is nonnegative. -/
theorem predictableLossAt_nonneg
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) (action : Action) :
    0 <= predictableLossAt loss t sample action := by
  cases t with
  | zero => exact loss.initial_nonneg sample.1 action
  | succ n =>
      exact loss.successor_nonneg n sample.1
        (Preorder.frestrictLe n sample.2) action

/-- Each generated realized scalar loss is at most one almost surely. -/
theorem sampledPredictableTrajectoryMeasure_realizedLoss_le_one_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu, sampledTrajectoryRealizedLossAt t sample <= 1 := by
  dsimp only
  have hreward := sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
    prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss t
  dsimp only at hreward
  filter_upwards [hreward] with sample hsample
  rw [hsample]
  exact (sampledTrajectorySelectedPredictableLossAt_mem_unitInterval
    loss t sample).2

/-- One common almost-sure event bounds every realized scalar loss strictly
before a finite horizon. -/
theorem sampledPredictableTrajectoryMeasure_finiteHorizon_realizedLoss_le_one_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu, ∀ t, t < horizon ->
      sampledTrajectoryRealizedLossAt t sample <= 1 := by
  dsimp only
  rw [ae_all_iff]
  intro t
  have hle := sampledPredictableTrajectoryMeasure_realizedLoss_le_one_ae
    prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss t
  dsimp only at hle
  filter_upwards [hle] with sample hsample
  intro _ht
  exact hsample

/-- Generated selected-loss regret against any comparator is at most the
horizon almost surely. -/
theorem sampledPredictable_realizedRegret_le_horizon_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu,
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryRealizedLossAt t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator) <=
        (horizon : Real) := by
  dsimp only
  have hreward :=
    sampledPredictableTrajectoryMeasure_finiteHorizon_realizedLoss_le_one_ae
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss horizon
  dsimp only at hreward
  filter_upwards [hreward] with sample hsample
  have hrealized :
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryRealizedLossAt t sample) <= (horizon : Real) := by
    calc
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryRealizedLossAt t sample) <=
          (Finset.range horizon).sum (fun _t => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hsample t (Finset.mem_range.mp ht)
      _ = (horizon : Real) := by simp
  have hcomparator :
      0 <= (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator) := by
    exact Finset.sum_nonneg fun t _ht =>
      predictableLossAt_nonneg loss t sample comparator
  linarith

/-- The strict `T + 1` threshold has zero failure probability under the
generated trajectory law. -/
theorem sampledPredictable_trivialRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (horizon : Nat) (delta : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    mu {sample |
        (horizon : Real) + 1 <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  have hregret := sampledPredictable_realizedRegret_le_horizon_ae
    prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss comparator
      horizon
  dsimp only at hregret
  have hzero :
      mu {sample |
          (horizon : Real) + 1 <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hregret] with sample hsample
    linarith
  rw [hzero]
  exact bot_le

/-- The regime in which the clipped explicit schedule satisfies the Bernstein
dominance contracts without activating its clip. -/
def bernsteinLargeHorizonCondition (K T delta : Real) : Prop :=
  8 * (K * Real.log K) <= T ∧
    8 * (K * Real.log (3 / delta)) <= T ∧
    8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (3 / delta) <= T

/-- All-horizon threshold: use the explicit Bernstein rate in its valid regime
and the strict pathwise horizon fallback otherwise. -/
noncomputable def bernsteinAllHorizonRegretThreshold
    (K T delta : Real) : Real := by
  classical
  exact if bernsteinLargeHorizonCondition K T delta then
    11 * bernsteinClippedExplorationRate K T delta * T
  else
    T + 1

/-- Generated realized-regret tail for every positive horizon. In the explicit
large-horizon regime the threshold is `11 * gamma * T`; otherwise the theorem
uses the genuine almost-sure `T` regret bound and threshold `T + 1`. -/
theorem sampledPredictable_allHorizonBernsteinRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let gamma := bernsteinClippedExplorationRate
      (arms.card : Real) (horizon : Real) delta
    let eta := bernsteinHighProbabilityLearningRate
      (arms.card : Real) (horizon : Real) gamma
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (bernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (bernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss.environment
    mu {sample |
        bernsteinAllHorizonRegretThreshold
            (arms.card : Real) (horizon : Real) delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  classical
  by_cases hlarge : bernsteinLargeHorizonCondition
      (arms.card : Real) (horizon : Real) delta
  · rw [bernsteinAllHorizonRegretThreshold, if_pos hlarge]
    exact
      sampledPredictable_explicitBernsteinRealizedHighProbabilityRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon hhorizon
          delta hdelta hdelta_le_one hlarge.1 hlarge.2.1 hlarge.2.2
  · rw [bernsteinAllHorizonRegretThreshold, if_neg hlarge]
    exact sampledPredictable_trivialRealizedRegret_tail
      prior arms harms
        (bernsteinHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real)
            (bernsteinClippedExplorationRate
              (arms.card : Real) (horizon : Real) delta))
        (bernsteinClippedExplorationRate
          (arms.card : Real) (horizon : Real) delta)
        (bernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (bernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss comparator horizon delta

end BanditRLProof.Exp3
