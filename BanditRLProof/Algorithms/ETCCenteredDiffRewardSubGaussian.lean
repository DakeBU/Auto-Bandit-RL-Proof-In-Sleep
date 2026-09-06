import BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail
import BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence

/-!
# ETC centered reward-difference sub-Gaussian transfer

This module transfers per-time centered reward sub-Gaussian witnesses through
the deterministic centered pairwise reward-difference transform used by the
ETC wrong-commit probability route.
-/

namespace BanditRLProof
namespace ETC

/--
Variance proxy induced on the centered pairwise reward-difference summand by
per-arm centered reward variance proxies.

Only the arm pulled by `ETC.actionWithCommit spec commitArm t` contributes:
arm `a`, the model best arm, or zero if neither is pulled at time `t`.
-/
noncomputable def centeredPairwiseRewardDiffVarianceProxy
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (cReward : Fin K -> Nat -> NNReal)
    (a : Fin K) (t : Nat) : NNReal :=
  if ETC.actionWithCommit spec commitArm t = a then cReward a t
  else if ETC.actionWithCommit spec commitArm t = model.bestArm then
    cReward model.bestArm t
  else 0

/--
Transfer a centered reward sub-Gaussian witness at one time index to the
corresponding centered pairwise reward-difference summand.

This is the `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` leaf. It handles
the deterministic action cases and the sign flip for the best-arm centered
reward. It does not prove the raw centered reward is sub-Gaussian from a
distributional model.
-/
theorem centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (cReward : Fin K -> Nat -> NNReal)
    (a : Fin K) (t : Nat)
    (hne : a = model.bestArm -> False)
    (h_subG :
      forall b : Fin K, ETC.actionWithCommit spec commitArm t = b ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega : Omega => (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega : Omega =>
        ETC.centeredPairwiseRewardDiff spec model commitArm reward a t omega)
      (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm cReward a t)
      mu := by
  classical
  have hane : Not (a = model.bestArm) := hne
  by_cases ha : ETC.actionWithCommit spec commitArm t = a
  · have hnot_best : Not (ETC.actionWithCommit spec commitArm t = model.bestArm) := by
      intro hbest
      exact hne (ha.symm.trans hbest)
    simpa [ETC.centeredPairwiseRewardDiffVarianceProxy,
      ETC.centeredPairwiseRewardDiff, ha, hnot_best, hane] using h_subG a ha
  · by_cases hbest : ETC.actionWithCommit spec commitArm t = model.bestArm
    · have hbest_ne_a : Not (model.bestArm = a) := by
        intro h
        exact hne h.symm
      have h := (h_subG model.bestArm hbest).neg
      have htarget :
          ProbabilityTheory.HasSubgaussianMGF
            (fun omega : Omega =>
              ((model.mean model.bestArm : Rat) : Real) - ((reward omega t : Rat) : Real))
            (cReward model.bestArm t) mu := by
        refine h.congr ?_
        exact Filter.Eventually.of_forall (fun omega => by
          simp [Pi.neg_apply, sub_eq_add_neg, add_comm])
      simpa [ETC.centeredPairwiseRewardDiffVarianceProxy,
        ETC.centeredPairwiseRewardDiff, ha, hbest, hbest_ne_a, Rat.cast_sub,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htarget
    · have hfun :
          (fun omega : Omega =>
            ETC.centeredPairwiseRewardDiff spec model commitArm reward a t omega) =
          (fun _omega : Omega => (0 : Real)) := by
        funext omega
        simp [ETC.centeredPairwiseRewardDiff, ha, hbest]
      rw [hfun]
      simp [ETC.centeredPairwiseRewardDiffVarianceProxy, ha, hbest]

/--
Canonical concrete argmax-oracle wrong-commit probability bound from
trace-level reward independence plus per-time centered reward sub-Gaussian
witnesses.

This is the `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` leaf. It composes
the reward-coordinate independence transfer, the centered reward sub-Gaussian
transfer, and the canonical wrong-commit probability consumer. It still leaves
the source of trace-level independence and centered reward sub-Gaussianity as
explicit assumptions.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
      [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (cReward : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_subG :
      forall b : Fin K, forall t, t < spec.explorationPulls * K ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega : Omega => (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm cReward)) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail
      hK mu spec model commitArm reward
      (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm cReward)
      hexplorationPulls_pos
      (ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward
        mu spec model commitArm reward h_reward_indep)
      (fun a hne t ht =>
        ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward
          mu spec model commitArm reward cReward a t hne
          (fun b _hb => h_reward_subG b t (Finset.mem_range.mp ht)))

end ETC
end BanditRLProof
