import BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian
import BanditRLProof.ConcentrationSubGaussian

/-!
# ETC bounded reward sub-Gaussian source

This module connects Mathlib's bounded-variable Hoeffding lemma to the ETC
reward-coordinate wrong-commit route. It still leaves the stochastic source of
reward-coordinate independence, boundedness, and mean identities explicit.
-/

namespace BanditRLProof
namespace ETC

/--
Sub-Gaussian variance proxy induced by an almost-sure interval bound on one
raw reward coordinate.
-/
noncomputable def centeredRewardBoundVarianceProxy
    {K : Nat}
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat) : NNReal :=
  ((nnnorm (hi a t - lo a t) / 2) ^ 2)

/--
An a.e. bounded raw reward coordinate is integrable.

This is the bounded-to-integrable source needed by the conditional mean-zero
route.  It is a thin ETC-shaped wrapper around Mathlib's
`MeasureTheory.Integrable.of_mem_Icc`.
-/
theorem centeredReward_integrable_of_mem_Icc
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat)
    (hmeas : AEMeasurable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (lo a t) (hi a t) (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu)) :
    MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu := by
  exact MeasureTheory.Integrable.of_mem_Icc (lo a t) (hi a t) hmeas hbound

/--
An exact raw-reward mean identity gives zero integral for the centered reward.

This is the zero-integral source needed by the conditional mean-zero wrapper.
It still keeps raw reward integrability explicit; boundedness or a concrete
reward law can discharge that assumption in later leaves.
-/
theorem centeredReward_integral_eq_zero_of_integral_eq_mean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat)
    (hint : MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hmean :
      MeasureTheory.integral mu
        (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t - model.mean a : Rat) : Real))) = 0 := by
  have hconst :
      MeasureTheory.Integrable
        (fun _omega : Omega => (((model.mean a : Rat) : Real))) mu :=
    MeasureTheory.integrable_const _
  calc
    MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega t - model.mean a : Rat) : Real))) =
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega t : Rat) : Real) -
            (((model.mean a : Rat) : Real)))) := by
        congr 1
        funext omega
        simp [Rat.cast_sub]
    _ =
      MeasureTheory.integral mu
        (fun omega : Omega => (((reward omega t : Rat) : Real))) -
      MeasureTheory.integral mu
        (fun _omega : Omega => (((model.mean a : Rat) : Real))) := by
        rw [MeasureTheory.integral_sub hint hconst]
    _ = 0 := by
        simp [hmean]

/--
Bounded reward plus the correct raw-reward mean identity gives zero integral
for the centered reward.

This combines the bounded-to-integrable source with the exact-mean
zero-integral wrapper.
-/
theorem centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat)
    (hmeas : AEMeasurable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (lo a t) (hi a t) (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu))
    (hmean : MeasureTheory.integral mu
      (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t - model.mean a : Rat) : Real))) = 0 := by
  exact
    ETC.centeredReward_integral_eq_zero_of_integral_eq_mean
      mu model reward a t
      (ETC.centeredReward_integrable_of_mem_Icc
        mu reward lo hi a t hmeas hbound)
      hmean

/--
Bounded reward plus the correct mean identity gives a centered reward
sub-Gaussian witness.

This is the `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` leaf. It is a
thin ETC-shaped wrapper around Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.
-/
theorem centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat)
    (hmeas : AEMeasurable (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (lo a t) (hi a t) (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu))
    (hmean : MeasureTheory.integral mu
      (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega : Omega => (((reward omega t - model.mean a : Rat) : Real)))
      (ETC.centeredRewardBoundVarianceProxy lo hi a t) mu := by
  simpa [ETC.centeredRewardBoundVarianceProxy, Concentration.intervalVarianceProxy,
    Rat.cast_sub] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (mu := mu)
      (X := fun omega : Omega => (((reward omega t : Rat) : Real)))
      (lo := lo a t)
      (hi := hi a t)
      (mean := (((model.mean a : Rat) : Real)))
      hmeas hbound hmean)

/--
Concrete argmax-oracle wrong-commit probability bound from reward-coordinate
independence, almost-sure bounded rewards, and exact per-coordinate mean
identities.

This is the `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` leaf. It
uses Mathlib's bounded-variable Hoeffding lemma only to produce the per-time
centered reward `HasSubgaussianMGF` witnesses consumed by the already compiled
reward-coordinate-law wrong-commit theorem.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_meas :
      forall _b : Fin K, forall t, t < spec.explorationPulls * K ->
        AEMeasurable (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (h_reward_bound :
      forall b : Fin K, forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun omega : Omega =>
            Set.Icc (lo b t) (hi b t) (((reward omega t : Rat) : Real)))
          (MeasureTheory.ae mu))
    (h_reward_mean :
      forall b : Fin K, forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral mu
          (fun omega : Omega => (((reward omega t : Rat) : Real))) =
          (((model.mean b : Rat) : Real))) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG
      hK mu spec model commitArm reward
      (ETC.centeredRewardBoundVarianceProxy lo hi)
      hexplorationPulls_pos h_reward_indep
      (fun b t ht =>
        ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean
          mu model reward lo hi b t
          (h_reward_meas b t ht)
          (h_reward_bound b t ht)
          (h_reward_mean b t ht))

/--
Concrete argmax-oracle wrong-commit probability bound from reward-coordinate
independence plus action-matched centered reward sub-Gaussian witnesses.

Unlike
`prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`,
this theorem only requires the centered witness for the arm actually pulled at
time `t`.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG
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
      forall t, t < spec.explorationPulls * K ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega : Omega =>
            (((reward omega t -
              model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real)))
          (cReward (ETC.actionWithCommit spec commitArm t) t) mu) :
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
          (fun b hb => by
            have h := h_reward_subG t (Finset.mem_range.mp ht)
            simpa [hb] using h))

/--
Concrete argmax-oracle wrong-commit probability bound from reward-coordinate
independence, action-matched almost-sure reward bounds, and action-matched
exact mean identities.

This is the practical fixed-commit ETC source boundary for a single observed
reward trace: `reward omega t` is centered at the mean of the arm actually
pulled at time `t`.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_meas :
      forall t, t < spec.explorationPulls * K ->
        AEMeasurable (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (h_reward_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun omega : Omega =>
            Set.Icc
              (lo (ETC.actionWithCommit spec commitArm t) t)
              (hi (ETC.actionWithCommit spec commitArm t) t)
              (((reward omega t : Rat) : Real)))
          (MeasureTheory.ae mu))
    (h_reward_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral mu
          (fun omega : Omega => (((reward omega t : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG
      hK mu spec model commitArm reward
      (ETC.centeredRewardBoundVarianceProxy lo hi)
      hexplorationPulls_pos h_reward_indep
      (fun t ht =>
        ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean
          mu model reward lo hi
          (ETC.actionWithCommit spec commitArm t) t
          (h_reward_meas t ht)
          (h_reward_bound t ht)
          (h_reward_mean t ht))

end ETC
end BanditRLProof
