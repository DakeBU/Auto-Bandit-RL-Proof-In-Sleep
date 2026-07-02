import BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses

/-!
# ETC centered reward-difference canonical sub-Gaussian tail

This module fixes the canonical exponential tail budget produced by the
centered reward-difference independent sub-Gaussian route.  It removes the
need for downstream users to provide a separate tail-domination hypothesis
when they choose the exact Mathlib sub-Gaussian bound as their tail function.
-/

namespace BanditRLProof
namespace ETC

/--
Canonical pairwise tail budget for the centered reward-difference independent
sub-Gaussian ETC route.

The expression is exactly the `ENNReal.ofReal (Real.exp ...)` right-hand side
used by the centered-diff producer over the ETC exploration horizon.
-/
noncomputable def centeredDiffSubGaussianTail
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (c : Fin K -> Nat -> NNReal)
    (a : Fin K) : ENNReal :=
  ENNReal.ofReal
    (Real.exp
      (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
        (2 *
          (((Finset.range (spec.explorationPulls * K)).sum
            (fun t => c a t) : NNReal) : Real))))

/--
Build the centered-diff witness package when the caller chooses the canonical
sub-Gaussian exponential tail budget.

This is the `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` leaf.  It still
requires the actual reward-law independence and sub-Gaussian witnesses, but it
discharges the tail-domination field definitionally.
-/
noncomputable def centeredDiffSubGaussianWitnesses_of_indep_subG
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (c : Fin K -> Nat -> NNReal)
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
    ETC.CenteredDiffSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model c) := by
  refine
    ⟨c, h_indep, h_subG, ?_⟩
  intro a _hne
  simp [ETC.centeredDiffSubGaussianTail]

/--
Produce the fixed-commit ETC pairwise empirical-mean tail contract directly
from concrete centered-diff independence and sub-Gaussian witnesses, using the
canonical exponential tail budget.

This theorem is the no-extra-tail-domination consumer for the independent
sub-Gaussian centered-diff route.
-/
theorem pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
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
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model c) := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model c)
      hexplorationPulls_pos
      (ETC.centeredDiffSubGaussianWitnesses_of_indep_subG
        mu spec model commitArm reward c h_indep h_subG)

end ETC
end BanditRLProof
