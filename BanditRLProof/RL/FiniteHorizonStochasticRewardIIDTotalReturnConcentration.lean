import BanditRLProof.RL.FiniteHorizonStochasticRewardInitialLawTotalReturnConcentration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# IID finite-horizon stochastic sampled-return concentration

This module takes finite products of complete reward-bearing trajectories.
Independence is only asserted across episodes. Each episode deviation remains
centered by the policy value at that trajectory's own sampled initial state.
-/

open MeasureTheory
open scoped ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace MDP

/-- The sampled-return deviation in one coordinate of a finite episode family. -/
noncomputable def sampledCumulativeReturnDeviationAtEpisode
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    {episodes : Nat} (episode : Fin episodes)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) : Real :=
  mdp.sampledCumulativeReturnDeviation policy (trajectories episode)

/-- One episode-coordinate deviation is measurable on the finite product space. -/
theorem measurable_sampledCumulativeReturnDeviationAtEpisode
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    {episodes : Nat} (episode : Fin episodes) :
    Measurable (mdp.sampledCumulativeReturnDeviationAtEpisode policy episode) := by
  exact (mdp.measurable_sampledCumulativeReturnDeviation policy).comp
    (measurable_pi_apply episode)

/-- Sum of sampled-return deviations over complete iid episode coordinates. -/
noncomputable def sampledCumulativeReturnDeviationSum
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (episodes : Nat)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) : Real :=
  ∑ episode : Fin episodes,
    mdp.sampledCumulativeReturnDeviationAtEpisode policy episode trajectories

/-- The finite-episode deviation sum is measurable. -/
theorem measurable_sampledCumulativeReturnDeviationSum
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (episodes : Nat) :
    Measurable (mdp.sampledCumulativeReturnDeviationSum policy episodes) := by
  exact Finset.measurable_sum Finset.univ fun episode _ =>
    mdp.measurable_sampledCumulativeReturnDeviationAtEpisode policy episode

/-- Episode-linear variance proxy for the iid sampled-return deviation sum. -/
noncomputable def iidSampledCumulativeReturnDeviationVarianceProxy
    (mdp : MDP State Action) (episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : NNReal :=
  (episodes : NNReal) *
    ((mdp.horizon : NNReal) * rewardVarianceProxy +
      meanBellmanInnovationVarianceProxy rewardBound mdp.horizon)

end MDP

namespace MDP
namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- Finite iid product of the complete reward-bearing stochastic trajectory law. -/
noncomputable def iidStochasticTrajectoryFamilyMeasure
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    Measure (Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) :=
  Measure.pi fun _episode : Fin episodes =>
    source.stochasticTrajectoryMeasure policy initialState

instance instIIDStochasticTrajectoryFamilyMeasureIsProbabilityMeasure
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    IsProbabilityMeasure
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  unfold iidStochasticTrajectoryFamilyMeasure
  infer_instance

/-- Every iid product coordinate has the exact complete stochastic trajectory law. -/
theorem iidStochasticTrajectoryFamilyMeasure_map_eval
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes) :
    (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes).map (Function.eval episode) =
      source.stochasticTrajectoryMeasure policy initialState := by
  exact
    (MeasureTheory.measurePreserving_eval
      (fun _episode : Fin episodes =>
        source.stochasticTrajectoryMeasure policy initialState)
      episode).map_eq

/-- Complete sampled-return deviations are independent across iid episodes. -/
theorem iIndepFun_sampledCumulativeReturnDeviationAtEpisode
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories =>
        mdp.sampledCumulativeReturnDeviationAtEpisode
          policy episode trajectories)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  unfold iidStochasticTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (mdp.measurable_sampledCumulativeReturnDeviation policy).aemeasurable

/-- Each iid episode coordinate inherits the compiled initial-law MGF. -/
theorem sampledCumulativeReturnDeviationAtEpisode_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy)
    {episodes : Nat} (episode : Fin episodes) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.sampledCumulativeReturnDeviationAtEpisode policy episode)
      ((mdp.horizon : NNReal) * rewardVarianceProxy +
        meanBellmanInnovationVarianceProxy rewardBound mdp.horizon)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  have hbase :=
    source.stochasticTrajectoryMeasure_sampledCumulativeReturnDeviation_hasSubgaussianMGF
      policy initialState rewardBound rewardVarianceProxy hrewardBound law
  rw [← source.iidStochasticTrajectoryFamilyMeasure_map_eval
    policy initialState episode] at hbase
  have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
    (μ := source.iidStochasticTrajectoryFamilyMeasure
      policy initialState episodes)
    (Y := Function.eval episode)
    (X := mdp.sampledCumulativeReturnDeviation policy)
    (c := (mdp.horizon : NNReal) * rewardVarianceProxy +
      meanBellmanInnovationVarianceProxy rewardBound mdp.horizon)
    (measurable_pi_apply episode).aemeasurable hbase
  simpa [MDP.sampledCumulativeReturnDeviationAtEpisode,
    Function.comp_def] using hlift

/-- The finite iid episode deviation sum has the episode-linear proxy. -/
theorem iidStochasticTrajectoryFamilyMeasure_sampledCumulativeReturnDeviationSum_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.sampledCumulativeReturnDeviationSum policy episodes)
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  have hindep :=
    source.iIndepFun_sampledCumulativeReturnDeviationAtEpisode
      policy initialState episodes
  have hsum :=
    ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
      (s := (Finset.univ : Finset (Fin episodes))) hindep
      (c := fun _episode =>
        (mdp.horizon : NNReal) * rewardVarianceProxy +
          meanBellmanInnovationVarianceProxy rewardBound mdp.horizon)
      (fun episode _ =>
        source.sampledCumulativeReturnDeviationAtEpisode_hasSubgaussianMGF
          policy initialState rewardBound rewardVarianceProxy
          hrewardBound law episode)
  simpa [MDP.sampledCumulativeReturnDeviationSum,
    MDP.iidSampledCumulativeReturnDeviationVarianceProxy, mul_add] using hsum

/-- Fixed-sample two-sided delta tail for the iid episode deviation sum. -/
theorem iidStochasticTrajectoryFamilyMeasure_sampledCumulativeReturnDeviationSum_abs_tail_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (htotal : 0 <
      ((mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
      {trajectories |
        Concentration.subGaussianSumConfidenceRadius
            (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
              episodes rewardBound rewardVarianceProxy) delta <=
          |mdp.sampledCumulativeReturnDeviationSum
            policy episodes trajectories|} <=
      ENNReal.ofReal delta := by
  let c : Fin episodes -> NNReal := fun _episode =>
    (mdp.horizon : NNReal) * rewardVarianceProxy +
      meanBellmanInnovationVarianceProxy rewardBound mdp.horizon
  have hindep :=
    source.iIndepFun_sampledCumulativeReturnDeviationAtEpisode
      policy initialState episodes
  have hsubG : forall episode, episode ∈ (Finset.univ : Finset (Fin episodes)) ->
      ProbabilityTheory.HasSubgaussianMGF
        (mdp.sampledCumulativeReturnDeviationAtEpisode policy episode)
        (c episode)
        (source.iidStochasticTrajectoryFamilyMeasure
          policy initialState episodes) := by
    intro episode _hepisode
    simpa [c] using
      source.sampledCumulativeReturnDeviationAtEpisode_hasSubgaussianMGF
        policy initialState rewardBound rewardVarianceProxy
        hrewardBound law episode
  have hvariance :
      0 < ((((Finset.univ : Finset (Fin episodes)).sum c : NNReal) : Real)) := by
    simpa [c, MDP.iidSampledCumulativeReturnDeviationVarianceProxy,
      mul_add] using htotal
  simpa [c, MDP.sampledCumulativeReturnDeviationSum,
    MDP.iidSampledCumulativeReturnDeviationVarianceProxy, mul_add] using
    (Concentration.subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes)
      hindep hsubG hvariance delta hdelta hdelta_le_one)

end MeanCompatibleRewardKernel
end MDP
end FiniteHorizonRL
end BanditRLProof
