import BanditRLProof.RL.FiniteHorizonStochasticRewardTrajectory

/-!
# Finite-horizon stochastic reward trajectory head marginals

This module identifies the first generated stochastic-reward coordinate at
every positive recursive horizon.  It exposes the exact action/reward joint
law and reward-only policy mixture needed before adding conditional-law or
concentration assumptions.
-/

open MeasureTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace RewardStepTrace

omit [Fintype State] [Fintype Action] in
/-- The first sampled action, reward, and next state of a positive trace. -/
def head (remaining : Nat) :
    RewardStepTrace Action State (remaining + 1) ->
      Prod Action (Prod Real State) :=
  fun trace => trace 0

omit [Fintype State] [Fintype Action] in
theorem measurable_head (remaining : Nat) :
    Measurable (head (Action := Action) (State := State) remaining) := by
  exact measurable_pi_apply 0

omit [Fintype State] [Fintype Action] in
/-- The first sampled action/reward pair, with next state discarded. -/
def headActionReward (remaining : Nat) :
    RewardStepTrace Action State (remaining + 1) -> Prod Action Real :=
  fun trace => ((trace 0).1, (trace 0).2.1)

omit [Fintype State] [Fintype Action] in
theorem measurable_headActionReward (remaining : Nat) :
    Measurable
      (headActionReward (Action := Action) (State := State) remaining) := by
  exact
    (measurable_fst.prodMk measurable_snd.fst).comp
      (measurable_pi_apply 0)

omit [Fintype State] [Fintype Action] in
/-- The first actual sampled Real reward of a positive trace. -/
def headReward (remaining : Nat) :
    RewardStepTrace Action State (remaining + 1) -> Real :=
  fun trace => (trace 0).2.1

omit [Fintype State] [Fintype Action] in
theorem measurable_headReward (remaining : Nat) :
    Measurable (headReward (Action := Action) (State := State) remaining) := by
  exact measurable_snd.fst.comp (measurable_pi_apply 0)

end RewardStepTrace

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- The action/reward marginal of one generated stochastic MDP step. -/
noncomputable def actionRewardKernel
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ProbabilityTheory.Kernel State (Prod Action Real) :=
  (source.actionRewardStateKernel policy stage).map
    (fun head => (head.1, head.2.1))

instance instActionRewardKernelIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel
      (source.actionRewardKernel policy stage) := by
  unfold actionRewardKernel
  apply ProbabilityTheory.Kernel.IsMarkovKernel.map
  exact measurable_fst.prodMk measurable_snd.fst

/-- The reward-only marginal after mixing the selected laws over policy actions. -/
noncomputable def rewardMarginalKernel
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ProbabilityTheory.Kernel State Real :=
  (source.actionRewardKernel policy stage).map Prod.snd

instance instRewardMarginalKernelIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel
      (source.rewardMarginalKernel policy stage) := by
  unfold rewardMarginalKernel
  apply ProbabilityTheory.Kernel.IsMarkovKernel.map
  exact measurable_snd

/-- The first generated coordinate has exactly the compiled one-step law. -/
theorem stochasticTrajectoryKernelRemaining_map_head
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state).map
        (RewardStepTrace.head (Action := Action) (State := State) remaining) =
      source.actionRewardStateKernel policy
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
  rw [stochasticTrajectoryKernelRemaining]
  rw [← ProbabilityTheory.Kernel.map_apply _
    (RewardStepTrace.measurable_head remaining)]
  rw [← ProbabilityTheory.Kernel.map_comp_right _
    (RewardStepTrace.measurable_cons remaining)
    (RewardStepTrace.measurable_head remaining)]
  change (((source.actionRewardStateKernel policy _).compProd _).map Prod.fst)
      state = _
  rw [← ProbabilityTheory.Kernel.fst_eq]
  rw [ProbabilityTheory.Kernel.fst_compProd]

/-- Mapping a generated trace to its first action/reward pair gives the joint marginal. -/
theorem stochasticTrajectoryKernelRemaining_map_headActionReward
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state).map
        (RewardStepTrace.headActionReward
          (Action := Action) (State := State) remaining) =
      source.actionRewardKernel policy
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
  let dropNext : Prod Action (Prod Real State) -> Prod Action Real :=
    fun head => (head.1, head.2.1)
  have hdropNext : Measurable dropNext :=
    measurable_fst.prodMk measurable_snd.fst
  calc
    _ = (Measure.map
          (RewardStepTrace.head (Action := Action) (State := State) remaining)
          (source.stochasticTrajectoryKernelRemaining policy
            (remaining + 1) hremaining state)).map dropNext := by
          rw [Measure.map_map hdropNext
            (RewardStepTrace.measurable_head remaining)]
          rfl
    _ = (source.actionRewardStateKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state).map dropNext := by
          rw [source.stochasticTrajectoryKernelRemaining_map_head
            policy remaining hremaining state]
    _ = source.actionRewardKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
          rw [actionRewardKernel,
            ProbabilityTheory.Kernel.map_apply _ hdropNext]

/-- Mapping a generated trace to its first reward gives the policy reward mixture. -/
theorem stochasticTrajectoryKernelRemaining_map_headReward
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state).map
        (RewardStepTrace.headReward
          (Action := Action) (State := State) remaining) =
      source.rewardMarginalKernel policy
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
  calc
    _ = (Measure.map
          (RewardStepTrace.headActionReward
            (Action := Action) (State := State) remaining)
          (source.stochasticTrajectoryKernelRemaining policy
            (remaining + 1) hremaining state)).map Prod.snd := by
          rw [Measure.map_map measurable_snd
            (RewardStepTrace.measurable_headActionReward remaining)]
          rfl
    _ = (source.actionRewardKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state).map Prod.snd := by
          rw [source.stochasticTrajectoryKernelRemaining_map_headActionReward
            policy remaining hremaining state]
    _ = source.rewardMarginalKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
          rw [rewardMarginalKernel,
            ProbabilityTheory.Kernel.map_apply _ measurable_snd]

/-- Exact action/reward rectangle law for a policy-mixed stochastic step. -/
theorem actionRewardKernel_apply_prod
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    (state : State) {actionSet : Set Action} {rewardSet : Set Real}
    (hactionSet : MeasurableSet actionSet)
    (hrewardSet : MeasurableSet rewardSet) :
    source.actionRewardKernel policy stage state (actionSet ×ˢ rewardSet) =
      ∫⁻ action in actionSet,
        source.rewardKernel.kernel (state, action) rewardSet
          ∂(policy.actionKernel stage state) := by
  let dropNext : Prod Action (Prod Real State) -> Prod Action Real :=
    fun head => (head.1, head.2.1)
  have hdropNext : Measurable dropNext :=
    measurable_fst.prodMk measurable_snd.fst
  rw [actionRewardKernel,
    ProbabilityTheory.Kernel.map_apply' _ hdropNext state
      (hactionSet.prod hrewardSet)]
  have hpreimage :
      dropNext ⁻¹' (actionSet ×ˢ rewardSet) =
        actionSet ×ˢ (rewardSet ×ˢ (Set.univ : Set State)) := by
    ext head
    simp [dropNext]
  rw [hpreimage, actionRewardStateKernel,
    ProbabilityTheory.Kernel.compProd_apply_prod hactionSet
      (hrewardSet.prod MeasurableSet.univ)]
  simp_rw [rewardNextStateKernel,
    ProbabilityTheory.Kernel.prod_apply_prod]
  simp

/-- Reward-event probability is the selected reward law mixed over policy actions. -/
theorem rewardMarginalKernel_apply
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    (state : State) {rewardSet : Set Real}
    (hrewardSet : MeasurableSet rewardSet) :
    source.rewardMarginalKernel policy stage state rewardSet =
      ∫⁻ action,
        source.rewardKernel.kernel (state, action) rewardSet
          ∂(policy.actionKernel stage state) := by
  rw [rewardMarginalKernel,
    ProbabilityTheory.Kernel.map_apply' _ measurable_snd state hrewardSet]
  have hpreimage :
      Prod.snd ⁻¹' rewardSet =
        (Set.univ : Set Action) ×ˢ rewardSet := by
    ext pair
    simp
  rw [hpreimage,
    source.actionRewardKernel_apply_prod policy stage state
      MeasurableSet.univ hrewardSet]
  simp

/--
Route endpoint: the generated first reward event has the exact randomized
policy mixture law, while the joint action/reward rectangle retains the
selected-law factorization.
-/
theorem stochasticTrajectoryKernelRemaining_headMarginalFactorization
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) {actionSet : Set Action} {rewardSet : Set Real}
    (hactionSet : MeasurableSet actionSet)
    (hrewardSet : MeasurableSet rewardSet) :
    (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state)
        ((RewardStepTrace.headActionReward
          (Action := Action) (State := State) remaining) ⁻¹'
            (actionSet ×ˢ rewardSet)) =
      ∫⁻ action in actionSet,
        source.rewardKernel.kernel (state, action) rewardSet
          ∂(policy.actionKernel
            ⟨mdp.horizon - (remaining + 1), by omega⟩ state) ∧
    (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state)
        ((RewardStepTrace.headReward
          (Action := Action) (State := State) remaining) ⁻¹' rewardSet) =
      ∫⁻ action,
        source.rewardKernel.kernel (state, action) rewardSet
          ∂(policy.actionKernel
            ⟨mdp.horizon - (remaining + 1), by omega⟩ state) := by
  constructor
  · rw [← Measure.map_apply
      (RewardStepTrace.measurable_headActionReward remaining)
      (hactionSet.prod hrewardSet)]
    rw [source.stochasticTrajectoryKernelRemaining_map_headActionReward
      policy remaining hremaining state]
    exact source.actionRewardKernel_apply_prod policy _ state
      hactionSet hrewardSet
  · rw [← Measure.map_apply
      (RewardStepTrace.measurable_headReward remaining) hrewardSet]
    rw [source.stochasticTrajectoryKernelRemaining_map_headReward
      policy remaining hremaining state]
    exact source.rewardMarginalKernel_apply policy _ state hrewardSet

end MDP.MeanCompatibleRewardKernel
end FiniteHorizonRL
end BanditRLProof
