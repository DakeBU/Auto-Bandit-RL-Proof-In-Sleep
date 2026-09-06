import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardTotalReturnConcentration

/-!
# Adaptive stochastic-reward realized behavior regret

This module changes the stochastic episode return from centering at each
sampled initial state's policy value to centering at the selected policy's
global initial-law value. The missing term is the policy-value fluctuation of
the sampled initial state. Complete episodes remain the independent units
inside one batch; no independence is assumed between the two terms inside an
episode or across adaptive rounds.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace MDP

/-- The sampled policy-value fluctuation at one complete episode coordinate. -/
noncomputable def initialPolicyValueDeviation
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State)
    (trajectory : State × RewardStepTrace Action State mdp.horizon) : Real :=
  policy.valueAt 0 (Nat.zero_le mdp.horizon) trajectory.1 -
    integral initialState (policy.valueAt 0 (Nat.zero_le mdp.horizon))

theorem measurable_initialPolicyValueDeviation
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) :
    Measurable (mdp.initialPolicyValueDeviation policy initialState) := by
  exact ((policy.measurable_valueAt 0 (Nat.zero_le mdp.horizon)).comp
    measurable_fst).sub measurable_const

/-- Hoeffding proxy for the policy value of one sampled initial state. -/
noncomputable def initialPolicyValueVarianceProxy
    (mdp : MDP State Action) (rewardBound : NNReal) : NNReal :=
  Concentration.intervalVarianceProxy
    (-((mdp.horizon : Real) * (rewardBound : Real)))
    ((mdp.horizon : Real) * (rewardBound : Real))

namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- The generated complete trajectory has the exact supplied initial marginal. -/
theorem stochasticTrajectoryMeasure_map_fst
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    (source.stochasticTrajectoryMeasure policy initialState).map Prod.fst =
      initialState := by
  unfold stochasticTrajectoryMeasure
  rw [← Measure.fst, Measure.fst_compProd]

/-- The initial-state policy-value fluctuation is sub-Gaussian. -/
theorem stochasticTrajectoryMeasure_initialPolicyValueDeviation_hasSubgaussianMGF
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real)) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.initialPolicyValueDeviation policy initialState)
      (mdp.initialPolicyValueVarianceProxy rewardBound)
      (source.stochasticTrajectoryMeasure policy initialState) := by
  let value := policy.valueAt 0 (Nat.zero_le mdp.horizon)
  have hbound : ∀ᵐ state ∂initialState,
      Set.Icc
        (-((mdp.horizon : Real) * (rewardBound : Real)))
        ((mdp.horizon : Real) * (rewardBound : Real))
        (value state) := by
    exact Filter.Eventually.of_forall fun state => by
      exact abs_le.mp (by
        simpa [value, MarkovPolicy.valueAt] using
          policy.valueRemaining_abs_le_of_rewardBound rewardBound hrewardBound
            mdp.horizon le_rfl state)
  have hbase : ProbabilityTheory.HasSubgaussianMGF
      (fun state => value state - integral initialState value)
      (mdp.initialPolicyValueVarianceProxy rewardBound) initialState := by
    simpa [MDP.initialPolicyValueVarianceProxy] using
      (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := initialState) (X := value)
        (mean := integral initialState value)
        (policy.measurable_valueAt 0
          (Nat.zero_le mdp.horizon)).aemeasurable hbound rfl)
  have hbaseMap : ProbabilityTheory.HasSubgaussianMGF
      (fun state => value state - integral initialState value)
      (mdp.initialPolicyValueVarianceProxy rewardBound)
      ((source.stochasticTrajectoryMeasure policy initialState).map Prod.fst) := by
    rw [source.stochasticTrajectoryMeasure_map_fst policy initialState]
    exact hbase
  have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
    (μ := source.stochasticTrajectoryMeasure policy initialState)
    (Y := Prod.fst)
    (X := fun state => value state - integral initialState value)
    measurable_fst.aemeasurable hbaseMap
  simpa [MDP.initialPolicyValueDeviation, value, Function.comp_def] using hlift

end MeanCompatibleRewardKernel

/-- Initial-state value fluctuation at one coordinate of an iid episode family. -/
noncomputable def initialPolicyValueDeviationAtEpisode
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) {episodes : Nat} (episode : Fin episodes)
    (trajectories : StochasticEpisodeBatch mdp episodes) : Real :=
  mdp.initialPolicyValueDeviation policy initialState (trajectories episode)

theorem measurable_initialPolicyValueDeviationAtEpisode
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) {episodes : Nat} (episode : Fin episodes) :
    Measurable
      (mdp.initialPolicyValueDeviationAtEpisode policy initialState episode) := by
  exact (mdp.measurable_initialPolicyValueDeviation policy initialState).comp
    (measurable_pi_apply episode)

/-- Sum of initial-state policy-value fluctuations in one iid batch. -/
noncomputable def initialPolicyValueDeviationSum
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) (episodes : Nat)
    (trajectories : StochasticEpisodeBatch mdp episodes) : Real :=
  ∑ episode : Fin episodes,
    mdp.initialPolicyValueDeviationAtEpisode
      policy initialState episode trajectories

theorem measurable_initialPolicyValueDeviationSum
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) (episodes : Nat) :
    Measurable
      (mdp.initialPolicyValueDeviationSum policy initialState episodes) := by
  exact Finset.measurable_sum Finset.univ fun episode _ =>
    mdp.measurable_initialPolicyValueDeviationAtEpisode
      policy initialState episode

/-- Episode-linear proxy for the initial-state value fluctuation sum. -/
noncomputable def iidInitialPolicyValueDeviationVarianceProxy
    (mdp : MDP State Action) (episodes : Nat)
    (rewardBound : NNReal) : NNReal :=
  (episodes : NNReal) * mdp.initialPolicyValueVarianceProxy rewardBound

/-- Sum of all sampled rewards in one complete stochastic episode batch. -/
def sampledCumulativeRewardSum
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : StochasticEpisodeBatch mdp episodes) : Real :=
  ∑ episode : Fin episodes,
    MeanCompatibleRewardKernel.sampledCumulativeReward
      (mdp := mdp) (trajectories episode)

theorem measurable_sampledCumulativeRewardSum
    (mdp : MDP State Action) (episodes : Nat) :
    Measurable (mdp.sampledCumulativeRewardSum episodes) := by
  exact Finset.measurable_sum Finset.univ fun episode _ =>
    MeanCompatibleRewardKernel.measurable_sampledCumulativeReward.comp
      (measurable_pi_apply episode)

/--
One batch's sampled return centered by the selected policy's global
initial-law value.
-/
noncomputable def globalSampledCumulativeReturnDeviationSum
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) (episodes : Nat)
    (trajectories : StochasticEpisodeBatch mdp episodes) : Real :=
  mdp.sampledCumulativeReturnDeviationSum policy episodes trajectories +
    mdp.initialPolicyValueDeviationSum
      policy initialState episodes trajectories

/-- The global batch deviation is actual sampled return minus its policy mean. -/
theorem globalSampledCumulativeReturnDeviationSum_eq
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) (episodes : Nat)
    (trajectories : StochasticEpisodeBatch mdp episodes) :
    mdp.globalSampledCumulativeReturnDeviationSum
        policy initialState episodes trajectories =
      mdp.sampledCumulativeRewardSum episodes trajectories -
        (episodes : Real) *
          integral initialState
            (policy.valueAt 0 (Nat.zero_le mdp.horizon)) := by
  unfold globalSampledCumulativeReturnDeviationSum
    sampledCumulativeReturnDeviationSum
    initialPolicyValueDeviationSum
  simp_rw [sampledCumulativeReturnDeviationAtEpisode,
    sampledCumulativeReturnDeviation,
    sampledCumulativeReturnDeviationFrom,
    initialPolicyValueDeviationAtEpisode,
    initialPolicyValueDeviation, MarkovPolicy.valueAt]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp [sampledCumulativeRewardSum,
    MeanCompatibleRewardKernel.sampledCumulativeReward]

theorem measurable_globalSampledCumulativeReturnDeviationSum
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) (episodes : Nat) :
    Measurable
      (mdp.globalSampledCumulativeReturnDeviationSum
        policy initialState episodes) := by
  exact (mdp.measurable_sampledCumulativeReturnDeviationSum policy episodes).add
    (mdp.measurable_initialPolicyValueDeviationSum
      policy initialState episodes)

/-- Honest same-space proxy for the two globally centered batch components. -/
noncomputable def iidGlobalSampledCumulativeReturnDeviationVarianceProxy
    (mdp : MDP State Action) (episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : NNReal :=
  ((mdp.iidSampledCumulativeReturnDeviationVarianceProxy
      episodes rewardBound rewardVarianceProxy).sqrt +
    (mdp.iidInitialPolicyValueDeviationVarianceProxy
      episodes rewardBound).sqrt) ^ 2

namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

theorem iIndepFun_initialPolicyValueDeviationAtEpisode
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories =>
        mdp.initialPolicyValueDeviationAtEpisode
          policy initialState episode trajectories)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  unfold iidStochasticTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (mdp.measurable_initialPolicyValueDeviation
      policy initialState).aemeasurable

theorem initialPolicyValueDeviationAtEpisode_hasSubgaussianMGF
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    {episodes : Nat} (episode : Fin episodes) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.initialPolicyValueDeviationAtEpisode
        policy initialState episode)
      (mdp.initialPolicyValueVarianceProxy rewardBound)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  have hbase :=
    source.stochasticTrajectoryMeasure_initialPolicyValueDeviation_hasSubgaussianMGF
      policy initialState rewardBound hrewardBound
  rw [← source.iidStochasticTrajectoryFamilyMeasure_map_eval
    policy initialState episode] at hbase
  have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
    (μ := source.iidStochasticTrajectoryFamilyMeasure
      policy initialState episodes)
    (Y := Function.eval episode)
    (X := mdp.initialPolicyValueDeviation policy initialState)
    (measurable_pi_apply episode).aemeasurable hbase
  simpa [MDP.initialPolicyValueDeviationAtEpisode,
    Function.comp_def] using hlift

theorem iidStochasticTrajectoryFamilyMeasure_initialPolicyValueDeviationSum_hasSubgaussianMGF
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real)) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.initialPolicyValueDeviationSum
        policy initialState episodes)
      (mdp.iidInitialPolicyValueDeviationVarianceProxy
        episodes rewardBound)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  have hindep := source.iIndepFun_initialPolicyValueDeviationAtEpisode
    policy initialState episodes
  have hsum := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
    (s := (Finset.univ : Finset (Fin episodes))) hindep
    (c := fun _episode => mdp.initialPolicyValueVarianceProxy rewardBound)
    (fun episode _ =>
      source.initialPolicyValueDeviationAtEpisode_hasSubgaussianMGF
        policy initialState rewardBound hrewardBound episode)
  simpa [MDP.initialPolicyValueDeviationSum,
    MDP.iidInitialPolicyValueDeviationVarianceProxy] using hsum

theorem iidStochasticTrajectoryFamilyMeasure_globalSampledCumulativeReturnDeviationSum_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.globalSampledCumulativeReturnDeviationSum
        policy initialState episodes)
      (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  have hreturn :=
    source.iidStochasticTrajectoryFamilyMeasure_sampledCumulativeReturnDeviationSum_hasSubgaussianMGF
      policy initialState episodes rewardBound rewardVarianceProxy
      hrewardBound law
  have hvalue :=
    source.iidStochasticTrajectoryFamilyMeasure_initialPolicyValueDeviationSum_hasSubgaussianMGF
      policy initialState episodes rewardBound hrewardBound
  simpa [MDP.globalSampledCumulativeReturnDeviationSum,
    MDP.iidGlobalSampledCumulativeReturnDeviationVarianceProxy] using
    hreturn.add hvalue

end MeanCompatibleRewardKernel
end MDP

namespace AdaptiveStochasticEpisodeBatchSource

/-- Explicit measurability of the history-selected globally centered batch return. -/
class GlobalReturnMeasurability
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes) :
    Prop where
  measurable_successorGlobalReturnDeviation : ∀ n,
    Measurable fun pair :
        StochasticEpisodeBatchPrefix mdp episodes n ×
          StochasticEpisodeBatch mdp episodes =>
      mdp.globalSampledCumulativeReturnDeviationSum
        (source.successorPolicy n pair.1) initialState episodes pair.2

/-- Dynamic globally centered return on a prefix/next-batch pair. -/
noncomputable def successorGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat)
    (pair : StochasticEpisodeBatchPrefix mdp episodes n ×
      StochasticEpisodeBatch mdp episodes) : Real :=
  mdp.globalSampledCumulativeReturnDeviationSum
    (source.successorPolicy n pair.1) initialState episodes pair.2

theorem measurable_successorGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] (n : Nat) :
    Measurable (source.successorGlobalReturnDeviation n) := by
  exact GlobalReturnMeasurability.measurable_successorGlobalReturnDeviation n

/-- Selected conditional law of the globally centered next-batch return. -/
noncomputable def successorGlobalReturnDeviationKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    ProbabilityTheory.Kernel
      (StochasticEpisodeBatchPrefix mdp episodes n) Real :=
  (ProbabilityTheory.Kernel.retainedInputKernel (source.batchKernel n)).map
    (source.successorGlobalReturnDeviation n)

instance instSuccessorGlobalReturnDeviationKernelIsMarkov
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] (n : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (source.successorGlobalReturnDeviationKernel n) := by
  unfold successorGlobalReturnDeviationKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (source.measurable_successorGlobalReturnDeviation n)

theorem successorGlobalReturnDeviationKernel_apply
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    source.successorGlobalReturnDeviationKernel n history =
      (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        (source.successorPolicy n history) initialState episodes).map
          (mdp.globalSampledCumulativeReturnDeviationSum
            (source.successorPolicy n history) initialState episodes) := by
  unfold successorGlobalReturnDeviationKernel
  rw [ProbabilityTheory.Kernel.map_apply
      (f := source.successorGlobalReturnDeviation n)
      (ProbabilityTheory.Kernel.retainedInputKernel (source.batchKernel n))
      (source.measurable_successorGlobalReturnDeviation n) history,
    ProbabilityTheory.Kernel.retainedInputKernel_apply]
  calc
    Measure.map (source.successorGlobalReturnDeviation n)
          (Measure.map (Prod.mk history) (source.batchKernel n history)) =
        Measure.map
          ((source.successorGlobalReturnDeviation n) ∘ Prod.mk history)
          (source.batchKernel n history) :=
      Measure.map_map
        (source.measurable_successorGlobalReturnDeviation n)
        (measurable_const.prodMk measurable_id)
    _ = (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
          (source.successorPolicy n history) initialState episodes).map
            (mdp.globalSampledCumulativeReturnDeviationSum
              (source.successorPolicy n history) initialState episodes) := by
      rw [source.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure]
      rfl

/-- Trajectory-level globally centered return at successor coordinate `n + 1`. -/
noncomputable def successorGlobalReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) : Real :=
  source.successorGlobalReturnDeviation n
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))

theorem measurable_successorGlobalReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] (n : Nat) :
    Measurable (source.successorGlobalReturnDeviationAt n) := by
  exact (source.measurable_successorGlobalReturnDeviation n).comp
    ((Preorder.measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1)))

theorem trajectoryMeasure_condDistrib_successorGlobalReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] (n : Nat) :
    ProbabilityTheory.condDistrib
        (source.successorGlobalReturnDeviationAt n)
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      source.successorGlobalReturnDeviationKernel n := by
  exact
    ProbabilityTheory.Kernel.condDistrib_dynamic_map_ae_eq_of_pair_map_eq_compProd
      source.trajectoryMeasure
      (Preorder.frestrictLe n)
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        trajectory (n + 1))
      (source.batchKernel n)
      (source.successorGlobalReturnDeviation n)
      (Preorder.measurable_frestrictLe n)
      (measurable_pi_apply (n + 1))
      (source.measurable_successorGlobalReturnDeviation n)
      (source.trajectoryMeasure_prefix_compProd n).symm

theorem condExpKernel_map_successorGlobalReturnDeviationAt_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] (n : Nat) :
    Filter.Eventually
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        Measure.map (source.successorGlobalReturnDeviationAt n)
            (ProbabilityTheory.condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (StochasticEpisodeBatchPrefix mdp episodes n)).comap
                  (Preorder.frestrictLe n)) trajectory) =
          source.successorGlobalReturnDeviationKernel n
            (Preorder.frestrictLe n trajectory))
      (ae (source.trajectoryMeasure.trim
        (Preorder.measurable_frestrictLe n).comap_le)) := by
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      source.trajectoryMeasure
      (source.successorGlobalReturnDeviationAt n)
      (Preorder.frestrictLe n)
      (source.measurable_successorGlobalReturnDeviationAt n)
      (Preorder.measurable_frestrictLe n)
      (source.successorGlobalReturnDeviationKernel n)
      (source.trajectoryMeasure_condDistrib_successorGlobalReturnDeviationAt n)

/-- Prefix process that deliberately leaves coordinate zero uncharged. -/
noncomputable def successorGlobalReturnPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes) :
    (round : Nat) → StochasticEpisodeBatchPrefix mdp episodes round → Real
  | 0, _history => 0
  | n + 1, history =>
      source.successorGlobalReturnDeviation n
        (Preorder.frestrictLe₂
          (π := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
          (Nat.le_succ n) history,
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem measurable_successorGlobalReturnPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] (round : Nat) :
    Measurable (source.successorGlobalReturnPrefixIncrement round) := by
  cases round with
  | zero =>
      simpa only [successorGlobalReturnPrefixIncrement] using
        (measurable_const : Measurable
          (fun _ : StochasticEpisodeBatchPrefix mdp episodes 0 => (0 : Real)))
  | succ n =>
      exact (source.measurable_successorGlobalReturnDeviation n).comp
        ((Preorder.measurable_frestrictLe₂
          (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
          (Nat.le_succ n)).prodMk
            (measurable_pi_apply
              (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))))

noncomputable def successorGlobalReturnIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (round : Nat)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) : Real :=
  source.successorGlobalReturnPrefixIncrement round
    (Preorder.frestrictLe round trajectory)

theorem successorGlobalReturnIncrement_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] :
    StronglyAdapted
      (Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes))
      source.successorGlobalReturnIncrement := by
  intro round
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact ((source.measurable_successorGlobalReturnPrefixIncrement round).comp
    (Measurable.of_comap_le le_rfl)).stronglyMeasurable

theorem successorGlobalReturnIncrement_succ_hasCondSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (n : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n)
      ((Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)).le n)
      (source.successorGlobalReturnIncrement (n + 1))
      (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let prefixMap : StochasticEpisodeBatchTrajectory mdp episodes →
      StochasticEpisodeBatchPrefix mdp episodes n := Preorder.frestrictLe n
  let X := source.successorGlobalReturnDeviationAt n
  let target : StochasticEpisodeBatchTrajectory mdp episodes → Measure Real :=
    fun trajectory =>
      source.successorGlobalReturnDeviationKernel n (prefixMap trajectory)
  let mcond : MeasurableSpace
      (StochasticEpisodeBatchTrajectory mdp episodes) :=
    (inferInstance : MeasurableSpace
      (StochasticEpisodeBatchPrefix mdp episodes n)).comap prefixMap
  have hmcond : mcond ≤ MeasurableSpace.pi := by
    simpa [mcond, prefixMap] using
      (Preorder.measurable_frestrictLe
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n).comap_le
  have hspace :
      Filtration.piLE
          (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n =
        mcond := by
    simpa [mcond, prefixMap] using
      (Filtration.piLE_eq_comap_frestrictLe
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n)
  have hkernel : Filter.Eventually
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        @Measure.map (StochasticEpisodeBatchTrajectory mdp episodes) Real
            MeasurableSpace.pi inferInstance X
            ((@ProbabilityTheory.condExpKernel
              (StochasticEpisodeBatchTrajectory mdp episodes)
              MeasurableSpace.pi _ source.trajectoryMeasure _ mcond)
                trajectory) =
          target trajectory)
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    simpa [X, target, prefixMap, mcond] using
      source.condExpKernel_map_successorGlobalReturnDeviationAt_eq n
  have htarget : Filter.Eventually
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        ProbabilityTheory.HasSubgaussianMGF id
          (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
            episodes rewardBound rewardVarianceProxy)
          (target trajectory))
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbase :=
        source.rewardSource.iidStochasticTrajectoryFamilyMeasure_globalSampledCumulativeReturnDeviationSum_hasSubgaussianMGF
          policy initialState episodes rewardBound rewardVarianceProxy
          hrewardBound law
      have hid :=
        (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
          (mdp.measurable_globalSampledCumulativeReturnDeviationSum
            policy initialState episodes).aemeasurable).2 hbase
      change ProbabilityTheory.HasSubgaussianMGF id
        (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          episodes rewardBound rewardVarianceProxy)
        (source.successorGlobalReturnDeviationKernel n history)
      rw [source.successorGlobalReturnDeviationKernel_apply n history]
      exact hid
  have hcondComap :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond hmcond X
      (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      (source.measurable_successorGlobalReturnDeviationAt n)
      target hkernel htarget
  have hcond :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_congr_measurableSpace
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond
      (Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n)
      hmcond
      ((Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)).le n)
      hspace.symm X
      (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      hcondComap
  simpa [successorGlobalReturnIncrement,
    successorGlobalReturnPrefixIncrement,
    successorGlobalReturnDeviationAt, X, prefixMap,
    Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply] using hcond

/-- Zero plus `rounds` successor proxies. -/
noncomputable def cumulativeSuccessorGlobalReturnVarianceProxy
    (mdp : MDP State Action) (rounds episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : NNReal :=
  ∑ t ∈ Finset.range (rounds + 1),
    match t with
    | 0 => 0
    | _ + 1 =>
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          episodes rewardBound rewardVarianceProxy

theorem cumulativeSuccessorGlobalReturnVarianceProxy_eq
    (mdp : MDP State Action) (rounds episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) :
    cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy =
      (rounds : NNReal) *
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          episodes rewardBound rewardVarianceProxy := by
  simp [cumulativeSuccessorGlobalReturnVarianceProxy,
    Finset.sum_range_succ']

/-- Cumulative globally centered deviation over successor coordinates only. -/
noncomputable def cumulativeSuccessorGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) : Real :=
  ∑ t ∈ Finset.range (rounds + 1),
    source.successorGlobalReturnIncrement t trajectory

theorem trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_abs_tail_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy)
    (htotal : 0 <
      ((cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    source.trajectoryMeasure
        {trajectory |
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
                rewardBound rewardVarianceProxy) delta ≤
            |source.cumulativeSuccessorGlobalReturnDeviation
              rounds trajectory|} ≤
      ENNReal.ofReal delta := by
  let F := Filtration.piLE
    (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
  let cY : Nat → NNReal := fun t =>
    match t with
    | 0 => 0
    | _ + 1 =>
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          episodes rewardBound rewardVarianceProxy
  have hadapted : StronglyAdapted F source.successorGlobalReturnIncrement := by
    simpa [F] using source.successorGlobalReturnIncrement_stronglyAdapted_piLE
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (source.successorGlobalReturnIncrement 0) (cY 0)
      source.trajectoryMeasure := by
    change ProbabilityTheory.HasSubgaussianMGF (fun _ => 0) 0
      source.trajectoryMeasure
    exact ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have hsucc : ∀ i, i < (rounds + 1) - 1 →
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (source.successorGlobalReturnIncrement (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.successorGlobalReturnIncrement_succ_hasCondSubgaussianMGF
        i rewardBound rewardVarianceProxy hrewardBound law
  have hvariance :
      0 < ((((Finset.range (rounds + 1)).sum cY : NNReal) : Real)) := by
    simpa [cY, cumulativeSuccessorGlobalReturnVarianceProxy] using htotal
  simpa [cumulativeSuccessorGlobalReturnVarianceProxy,
    cumulativeSuccessorGlobalReturnDeviation, cY] using
    (Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      hadapted hzero (rounds + 1) hsucc hvariance
      delta hdelta hdelta_le_one)

/-- The selected successor policy after observing coordinates through `n`. -/
noncomputable def successorPolicyAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) (n : Nat) :
    MarkovPolicy mdp :=
  source.successorPolicy n (Preorder.frestrictLe n trajectory)

/-- Optimal expected return under the supplied initial-state law. -/
noncomputable def optimalInitialExpectedReturn
    [Nonempty Action]
    (mdp : MDP State Action) (initialState : Measure State) : Real :=
  integral initialState
    (mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon))

/-- Sum of selected successor-policy expected regrets. -/
noncomputable def successorExpectedCumulativeRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] [Nonempty Action] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (source.successorPolicyAt trajectory round).expectedRegret initialState

/-- Average selected successor-policy expected regret per adaptive round. -/
noncomputable def successorExpectedAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] [Nonempty Action] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) : Real :=
  source.successorExpectedCumulativeRegret trajectory rounds / (rounds : Real)

/-- Realized regret of all sampled successor batches. -/
noncomputable def realizedSuccessorCumulativeRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] [Nonempty Action] {episodes : Nat}
    (_source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    ((episodes : Real) * optimalInitialExpectedReturn mdp initialState -
      mdp.sampledCumulativeRewardSum episodes
        (trajectory ((round : Nat) + 1)))

/-- Realized successor regret averaged over sampled episodes and rounds. -/
noncomputable def realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] [Nonempty Action] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) : Real :=
  source.realizedSuccessorCumulativeRegret trajectory rounds /
    ((episodes : Real) * (rounds : Real))

/-- The adaptive successor increment is actual batch return minus policy mean. -/
theorem successorGlobalReturnIncrement_succ_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) (n : Nat) :
    source.successorGlobalReturnIncrement (n + 1) trajectory =
      mdp.sampledCumulativeRewardSum episodes (trajectory (n + 1)) -
        (episodes : Real) *
          integral initialState
            ((source.successorPolicyAt trajectory n).valueAt
              0 (Nat.zero_le mdp.horizon)) := by
  simp only [successorGlobalReturnIncrement,
    successorGlobalReturnPrefixIncrement, successorGlobalReturnDeviation,
    successorPolicyAt, Preorder.frestrictLe_apply]
  exact mdp.globalSampledCumulativeReturnDeviationSum_eq
    (source.successorPolicy n (Preorder.frestrictLe n trajectory))
    initialState episodes (trajectory (n + 1))

/-- The cumulative deviation is the finite sum over successor coordinates. -/
theorem cumulativeSuccessorGlobalReturnDeviation_eq_fin_sum
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory =
      ∑ round : Fin rounds,
        source.successorGlobalReturnIncrement ((round : Nat) + 1) trajectory := by
  unfold cumulativeSuccessorGlobalReturnDeviation
  rw [Finset.sum_range_succ']
  simp only [successorGlobalReturnIncrement,
    successorGlobalReturnPrefixIncrement, add_zero]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro round hround
  have hround_lt : round < rounds := Finset.mem_range.mp hround
  rw [dif_pos hround_lt]

/-- Exact realized equals expected minus globally centered return deviation. -/
theorem realizedSuccessorCumulativeRegret_eq_expected_sub_deviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] [Nonempty Action] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    source.realizedSuccessorCumulativeRegret trajectory rounds =
      (episodes : Real) *
          source.successorExpectedCumulativeRegret trajectory rounds -
        source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory := by
  rw [source.cumulativeSuccessorGlobalReturnDeviation_eq_fin_sum]
  unfold realizedSuccessorCumulativeRegret successorExpectedCumulativeRegret
  calc
    (∑ round : Fin rounds,
        ((episodes : Real) * optimalInitialExpectedReturn mdp initialState -
          mdp.sampledCumulativeRewardSum episodes
            (trajectory ((round : Nat) + 1)))) =
        ∑ round : Fin rounds,
          ((episodes : Real) *
              (source.successorPolicyAt trajectory round).expectedRegret
                initialState -
            source.successorGlobalReturnIncrement
              ((round : Nat) + 1) trajectory) := by
      apply Finset.sum_congr rfl
      intro round _hround
      rw [source.successorGlobalReturnIncrement_succ_eq]
      unfold MarkovPolicy.expectedRegret optimalInitialExpectedReturn
      rw [(source.successorPolicyAt trajectory round).integral_cumulativeReward_trajectoryMeasure_eq_integral_valueAt_zero]
      ring
    _ = (episodes : Real) *
          (∑ round : Fin rounds,
            (source.successorPolicyAt trajectory round).expectedRegret
              initialState) -
        ∑ round : Fin rounds,
          source.successorGlobalReturnIncrement
            ((round : Nat) + 1) trajectory := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Exact averaged form of the stochastic realized-regret decomposition. -/
theorem realizedSuccessorAverageRegret_eq_expected_sub_deviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] [Nonempty Action] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes) :
    source.realizedSuccessorAverageRegret trajectory rounds =
      source.successorExpectedAverageRegret trajectory rounds -
        source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
          ((episodes : Real) * (rounds : Real)) := by
  have hroundsReal : (rounds : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt hrounds)
  have hepisodesReal : (episodes : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt hepisodes)
  rw [realizedSuccessorAverageRegret, successorExpectedAverageRegret,
    source.realizedSuccessorCumulativeRegret_eq_expected_sub_deviation]
  field_simp

/-- Return-deviation event used by fixed-window stochastic regret transport. -/
noncomputable def successorGlobalReturnDeviationBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (delta : Real) : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
  {trajectory |
    Concentration.subGaussianSumConfidenceRadius
        (cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
          rewardBound rewardVarianceProxy) delta ≤
      |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory|}

theorem measurable_cumulativeSuccessorGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability] (rounds : Nat) :
    Measurable (source.cumulativeSuccessorGlobalReturnDeviation rounds) := by
  refine Finset.measurable_sum (Finset.range (rounds + 1)) fun t _ => ?_
  exact (((source.successorGlobalReturnIncrement_stronglyAdapted_piLE t).mono
    ((Filtration.piLE
      (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)).le t)).measurable)

theorem measurableSet_successorGlobalReturnDeviationBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (delta : Real) :
    MeasurableSet (source.successorGlobalReturnDeviationBadEvent
      rounds rewardBound rewardVarianceProxy delta) := by
  exact measurableSet_le measurable_const
    (source.measurable_cumulativeSuccessorGlobalReturnDeviation rounds).abs

theorem trajectoryMeasure_successorGlobalReturnDeviationBadEvent_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (htotal : 0 <
      ((cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    source.trajectoryMeasure
        (source.successorGlobalReturnDeviationBadEvent
          rounds rewardBound rewardVarianceProxy delta) ≤
      ENNReal.ofReal delta := by
  simpa only [successorGlobalReturnDeviationBadEvent] using
    source.trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_abs_tail_le
      rounds rewardBound rewardVarianceProxy hrewardBound law htotal
      delta hdelta hdelta_le_one

/--
Combine a caller-supplied count/optimism event with the stochastic return event.
-/
theorem trajectoryMeasure_expected_to_realized_successor_average_regret_transport
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (htotal : 0 <
      ((cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (countBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes))
    (expectedBound : Real)
    (Good : StochasticEpisodeBatchTrajectory mdp episodes → Prop)
    (hcountMeasurable : MeasurableSet countBadEvent)
    (hcountTail : source.trajectoryMeasure countBadEvent ≤ ENNReal.ofReal delta)
    (hcountGood : ∀ trajectory, trajectory ∉ countBadEvent →
      Good trajectory ∧
        source.successorExpectedAverageRegret trajectory rounds ≤ expectedBound) :
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds rewardBound rewardVarianceProxy delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent ∧
      source.trajectoryMeasure combinedBadEvent ≤
        ENNReal.ofReal delta + ENNReal.ofReal delta ∧
      ∀ trajectory, trajectory ∉ combinedBadEvent →
        Good trajectory ∧
          source.realizedSuccessorAverageRegret trajectory rounds ≤
            expectedBound +
              Concentration.subGaussianSumConfidenceRadius
                  (cumulativeSuccessorGlobalReturnVarianceProxy
                    mdp rounds episodes rewardBound rewardVarianceProxy) delta /
                ((episodes : Real) * (rounds : Real)) := by
  let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
    rounds rewardBound rewardVarianceProxy delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  have hreturnMeasurable : MeasurableSet returnBadEvent := by
    simpa [returnBadEvent] using
      source.measurableSet_successorGlobalReturnDeviationBadEvent
        rounds rewardBound rewardVarianceProxy delta
  have hreturnTail : source.trajectoryMeasure returnBadEvent ≤
      ENNReal.ofReal delta := by
    simpa [returnBadEvent] using
      source.trajectoryMeasure_successorGlobalReturnDeviationBadEvent_le
        rounds rewardBound rewardVarianceProxy hrewardBound law htotal
        delta hdelta hdelta_le_one
  refine ⟨hcountMeasurable.union hreturnMeasurable, ?_, ?_⟩
  · exact (measure_union_le countBadEvent returnBadEvent).trans
      (add_le_add hcountTail hreturnTail)
  · intro trajectory htrajectory
    have hnotCount : trajectory ∉ countBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_left returnBadEvent hmem)
    have hnotReturn : trajectory ∉ returnBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_right countBadEvent hmem)
    have hgood := hcountGood trajectory hnotCount
    refine ⟨hgood.1, ?_⟩
    have hdeviation :
        |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <
          Concentration.subGaussianSumConfidenceRadius
            (cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes rewardBound rewardVarianceProxy) delta := by
      exact lt_of_not_ge (by simpa [returnBadEvent,
        successorGlobalReturnDeviationBadEvent] using hnotReturn)
    have hdenom : 0 < (episodes : Real) * (rounds : Real) := by
      positivity
    rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
      trajectory rounds hrounds hepisodes]
    have hnoise :
        -source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) ≤
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound rewardVarianceProxy) delta /
            ((episodes : Real) * (rounds : Real)) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      exact (neg_le_abs _).trans hdeviation.le
    calc
      source.successorExpectedAverageRegret trajectory rounds -
          source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) =
        source.successorExpectedAverageRegret trajectory rounds +
          (-source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real))) := by ring
      _ ≤ source.successorExpectedAverageRegret trajectory rounds +
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound rewardVarianceProxy) delta /
            ((episodes : Real) * (rounds : Real)) :=
        add_le_add le_rfl hnoise
      _ ≤ expectedBound +
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound rewardVarianceProxy) delta /
            ((episodes : Real) * (rounds : Real)) :=
        add_le_add hgood.2 le_rfl

end AdaptiveStochasticEpisodeBatchSource

end FiniteHorizonRL
end BanditRLProof
