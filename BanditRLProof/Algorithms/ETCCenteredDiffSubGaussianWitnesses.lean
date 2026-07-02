import BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail

/-!
# ETC centered reward-difference sub-Gaussian witness surface

This module packages the concrete reward-law witnesses needed by the centered
reward-difference ETC tail producer.  It does not prove those witnesses from a
reward distribution, filtration, or kernel.  Instead, it gives downstream work
one exact Lean-facing contract to target.
-/

namespace BanditRLProof
namespace ETC

/--
Witness package for the concrete centered reward-difference sub-Gaussian ETC
tail route.

This is the `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` leaf.  The fields
are exactly the reward-law facts still missing after the compiled centered-diff
producer specialization: a sub-Gaussian variance proxy, independence of the
centered summands, per-index sub-Gaussian MGF witnesses on the exploration
horizon, and domination by the chosen pairwise tail budget.
-/
structure CenteredDiffSubGaussianWitnesses
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal) where
  c : Fin K -> Nat -> NNReal
  indep :
    forall a : Fin K, (a = model.bestArm -> False) ->
      ProbabilityTheory.iIndepFun
        (fun t omega =>
          ETC.centeredPairwiseRewardDiff
            spec model commitArm reward a t omega)
        mu
  subG :
    forall a : Fin K, (a = model.bestArm -> False) ->
      forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)
          (c a t) mu
  tail_bound :
    forall a : Fin K, (a = model.bestArm -> False) ->
      ENNReal.ofReal
        (Real.exp
          (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
            (2 *
              (((Finset.range (spec.explorationPulls * K)).sum
                (fun t => c a t) : NNReal) : Real)))) <= tail a

/--
Consume a centered reward-difference witness package to build the fixed-commit
ETC pairwise empirical-mean tail contract.

This theorem is intentionally thin.  It fixes the exact API boundary for the
next reward-law leaf while reusing the already compiled centered-diff producer.
-/
theorem pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (w :
      ETC.CenteredDiffSubGaussianWitnesses
        mu spec model commitArm reward tail) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds
      mu spec model commitArm reward tail w.c hexplorationPulls_pos
      w.indep w.subG w.tail_bound

end ETC
end BanditRLProof
