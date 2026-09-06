import BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail

/-!
# ETC wrong-commit probability with the canonical centered-diff tail

This module closes the local composition from the canonical centered reward
difference independent sub-Gaussian route to the concrete argmax-oracle
wrong-commit probability bound. It still leaves the actual reward-law
independence and sub-Gaussian witnesses as explicit hypotheses.
-/

namespace BanditRLProof
namespace ETC

/--
Concrete argmax-oracle wrong-commit probability bound using the canonical
centered reward-difference sub-Gaussian tail budget.

This is the `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` leaf. It composes
the compiled canonical centered-diff producer with the compiled filtered-sum
wrong-commit probability consumer. It does not prove the reward-law
independence or `HasSubgaussianMGF` witnesses.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
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
            (c a t) mu) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model c) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract
      hK
      mu
      spec
      model
      commitArm
      reward
      (ETC.centeredDiffSubGaussianTail spec model c)
      (ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG
        mu spec model commitArm reward c hexplorationPulls_pos h_indep h_subG)

end ETC
end BanditRLProof
