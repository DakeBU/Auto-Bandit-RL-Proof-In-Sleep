import BanditRLProof.Algorithms.ETCPairwiseSubGaussianTail
import BanditRLProof.Algorithms.ETCSumRewardsDiff
import BanditRLProof.FiniteBanditModelInvariants

/-!
# ETC centered reward-difference sub-Gaussian tail producer

This module specializes the abstract ETC pairwise sub-Gaussian producer to the
compiled centered reward-difference finite-sum event.  It keeps the actual
probabilistic reward-law work explicit: independence and sub-Gaussian witnesses
for the concrete summands remain hypotheses.
-/

namespace BanditRLProof
namespace ETC

/--
Build the fixed-commit ETC pairwise empirical-mean tail contract from concrete
centered pairwise reward-difference sub-Gaussian witnesses over the ETC
exploration horizon.

This is the `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` bridge.  It instantiates
the abstract producer with
`idx := Finset.range (spec.explorationPulls * K)`,
`X := ETC.centeredPairwiseRewardDiff`, and
`eps := ETC.centeredPairwiseGapThreshold`.  It still does not prove
independence, sub-Gaussianity of reward differences, filtration, or final ETC
regret.
-/
theorem pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (c : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun
          (fun t omega =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)
          mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
          ProbabilityTheory.HasSubgaussianMGF
            (fun omega =>
              ETC.centeredPairwiseRewardDiff
                spec model commitArm reward a t omega)
            (c a t) mu)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t => c a t) : NNReal) : Real)))) <= tail a) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  refine
    ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds
      (mu := mu)
      (spec := spec)
      (model := model)
      (commitArm := commitArm)
      (reward := reward)
      (tail := tail)
      (idx := Finset.range (spec.explorationPulls * K))
      (X := fun a t omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      (c := c)
      (eps := fun a => ETC.centeredPairwiseGapThreshold spec model a)
      ?h_indep ?h_subG ?heps ?hsubset ?htail
  · exact h_indep
  · exact h_subG
  · intro a _hne
    unfold ETC.centeredPairwiseGapThreshold
    exact
      (Rat.cast_nonneg (K := Real)).2
        (mul_nonneg
          (Nat.cast_nonneg spec.explorationPulls)
          (sub_nonneg.mpr
            (FiniteBanditModel.mean_le_bestArm_mean model a)))
  · intro a _hne
    exact
      ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event
        spec model commitArm reward a hexplorationPulls_pos
  · exact htail

end ETC
end BanditRLProof
