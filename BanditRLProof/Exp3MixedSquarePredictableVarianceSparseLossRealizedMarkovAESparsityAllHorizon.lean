import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAllHorizon

/-!
# All-horizon sparse-loss EXP3 under almost-everywhere sparsity

This module replaces the universal pathwise sparse-support contract of the
existing all-horizon route by an almost-everywhere contract under the exact
generated trajectory measure. The large-horizon branch combines the compiled
raw sparse-loss tail with the tuned and explicit budget comparisons. The
complementary branch keeps the strict `T + 1` zero-probability fallback.

The exceptional sparsity set has measure zero, so this transport spends no
additional failure probability. The result still uses the armwise aggregate
loss mass and Markov's polynomial confidence dependence; it is not a
best-arm first-order or Freedman/EXP3.P theorem.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Generated sparse-loss realized-regret tail for every positive horizon when
support sparsity holds almost everywhere under the exact internally tuned
trajectory measure. -/
theorem sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_ae_sparsity
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let gamma := sparseLossPredictableVarianceClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta := sparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (sparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (sparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    (∀ᵐ sample ∂mu, ∀ t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card <= sparsity) →
    mu {sample |
        sparseLossPredictableVarianceAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  intro hsparse
  classical
  let gamma := sparseLossPredictableVarianceClippedExplorationRate
    (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  let eta := sparseLossPredictableVarianceHighProbabilityLearningRate
    arms gamma horizon sparsity delta
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hS : 0 < (sparsity : Real) := by exact_mod_cast hsparsity
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hgamma_pos : 0 < gamma := by
    exact sparseLossPredictableVarianceClippedExplorationRate_pos
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
        hK_one hS hT
  have hgamma_le_half : gamma <= 1 / 2 := by
    exact sparseLossPredictableVarianceClippedExplorationRate_le_half
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  have hgamma_lt_one : gamma < 1 := by linarith
  by_cases hlarge : sparseLossPredictableVarianceLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  · rw [sparseLossPredictableVarianceAllHorizonRegretThreshold,
      if_pos hlarge]
    have hcontracts :=
      sparseLossPredictableVarianceClippedExplorationRate_contracts
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          hK_one hS hT hdelta hdelta_le_one hlarge.1 hlarge.2.1
            hlarge.2.2.1 hlarge.2.2.2
    dsimp only at hcontracts
    rcases hcontracts with
      ⟨_hgamma_pos, _hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
    have heta : 0 < eta := by
      exact sparseLossPredictableVarianceHighProbabilityLearningRate_pos
        arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
          delta hdelta
    have hraw_to_tuned :=
      sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget_le_tunedThreshold
        arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
          hhorizon hsparsity delta hdelta
    have htuned_to_explicit :=
      sparseLossPredictableVarianceRealizedMarkovTunedThreshold_le_explicitThreshold
        arms hcard_two horizon sparsity hhorizon hsparsity gamma delta
          hgamma_pos hgamma_le_half hdelta hdelta_le_one hbase hmixed
            hconfidence hrealized
    have htail :=
      sampledPredictable_predictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegret_tail_total_delta_of_ae_sparsity
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon sparsity hhorizon hsparsity delta hdelta hsparse
    dsimp only [eta, gamma] at htail ⊢
    calc
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
          (sparseLossPredictableVarianceHighProbabilityLearningRate
            arms
              (sparseLossPredictableVarianceClippedExplorationRate
                (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
              horizon sparsity delta)
          (sparseLossPredictableVarianceClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
          hgamma_pos.le hgamma_lt_one.le loss.environment)
          {sample |
            sparseLossPredictableVarianceRealizedMarkovExplicitThreshold
                arms
                  (sparseLossPredictableVarianceClippedExplorationRate
                    (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
                horizon sparsity delta <=
              (Finset.range horizon).sum (fun t =>
                  sampledTrajectoryRealizedLossAt t sample) -
                (Finset.range horizon).sum (fun t =>
                  predictableLossAt loss t sample comparator)} <=
        (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
          (sparseLossPredictableVarianceHighProbabilityLearningRate
            arms
              (sparseLossPredictableVarianceClippedExplorationRate
                (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
              horizon sparsity delta)
          (sparseLossPredictableVarianceClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
          hgamma_pos.le hgamma_lt_one.le loss.environment)
          {sample |
            sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget
                arms
                  (sparseLossPredictableVarianceHighProbabilityLearningRate
                    arms
                      (sparseLossPredictableVarianceClippedExplorationRate
                        (arms.card : Real) (sparsity : Real)
                          (horizon : Real) delta)
                      horizon sparsity delta)
                  (sparseLossPredictableVarianceClippedExplorationRate
                    (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
                horizon sparsity delta <=
              (Finset.range horizon).sum (fun t =>
                  sampledTrajectoryRealizedLossAt t sample) -
                (Finset.range horizon).sum (fun t =>
                  predictableLossAt loss t sample comparator)} := by
          apply measure_mono
          intro sample hsample
          exact hraw_to_tuned.trans (htuned_to_explicit.trans hsample)
      _ <= ENNReal.ofReal delta := htail
  · rw [sparseLossPredictableVarianceAllHorizonRegretThreshold,
      if_neg hlarge]
    exact sampledPredictable_trivialRealizedRegret_tail
      prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le
        loss comparator horizon delta

end BanditRLProof.Exp3
