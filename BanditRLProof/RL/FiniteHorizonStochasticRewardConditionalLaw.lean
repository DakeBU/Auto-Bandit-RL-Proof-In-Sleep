import BanditRLProof.RL.FiniteHorizonStochasticRewardMarginal
import BanditRLProof.ConditionalExpectationReward

/-!
# Finite-horizon stochastic reward trajectory head conditional law

This module identifies the selected reward kernel as the conditional law of
the first sampled reward given the first sampled action.  The result is first
proved for the one-step action/reward marginal, then transported to every
positive generated stochastic trajectory and to the corresponding trimmed
`condExpKernel.map` surface.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace RewardStepTrace

omit [Fintype State] [Fintype Action] in
/-- The first sampled action of a positive reward-bearing trace. -/
def headAction (remaining : Nat) :
    RewardStepTrace Action State (remaining + 1) -> Action :=
  fun trace => (trace 0).1

omit [Fintype State] [Fintype Action] in
theorem measurable_headAction (remaining : Nat) :
    Measurable (headAction (Action := Action) (State := State) remaining) := by
  exact measurable_fst.comp (measurable_pi_apply 0)

end RewardStepTrace

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- The reward kernel selected after freezing the current state. -/
noncomputable def selectedRewardKernelAt
    (source : MeanCompatibleRewardKernel mdp) (state : State) :
    ProbabilityTheory.Kernel Action Real :=
  ProbabilityTheory.Kernel.sectR source.rewardKernel.kernel state

instance instSelectedRewardKernelAtIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp) (state : State) :
    ProbabilityTheory.IsMarkovKernel
      (source.selectedRewardKernelAt state) := by
  unfold selectedRewardKernelAt
  infer_instance

/-- The one-step action/reward marginal is the policy law composed with the selected reward law. -/
theorem actionRewardKernel_eq_compProd_selectedRewardKernelAt
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    (state : State) :
    source.actionRewardKernel policy stage state =
      policy.actionKernel stage state ⊗ₘ source.selectedRewardKernelAt state := by
  apply Measure.ext_prod
  intro actionSet rewardSet hactionSet hrewardSet
  rw [source.actionRewardKernel_apply_prod policy stage state
    hactionSet hrewardSet]
  rw [Measure.compProd_apply_prod hactionSet hrewardSet]
  rfl

/-- The action marginal of the one-step action/reward law is the policy action law. -/
theorem actionRewardKernel_map_fst
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    (state : State) :
    (source.actionRewardKernel policy stage state).map Prod.fst =
      policy.actionKernel stage state := by
  rw [source.actionRewardKernel_eq_compProd_selectedRewardKernelAt]
  change
    (policy.actionKernel stage state ⊗ₘ
      source.selectedRewardKernelAt state).fst = _
  rw [Measure.fst_compProd]

/-- Mapping a generated trace to its first action recovers the policy action law. -/
theorem stochasticTrajectoryKernelRemaining_map_headAction
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state).map
        (RewardStepTrace.headAction
          (Action := Action) (State := State) remaining) =
      policy.actionKernel
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
  calc
    _ = (Measure.map
          (RewardStepTrace.headActionReward
            (Action := Action) (State := State) remaining)
          (source.stochasticTrajectoryKernelRemaining policy
            (remaining + 1) hremaining state)).map Prod.fst := by
          rw [Measure.map_map measurable_fst
            (RewardStepTrace.measurable_headActionReward remaining)]
          rfl
    _ = (source.actionRewardKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state).map Prod.fst := by
          rw [source.stochasticTrajectoryKernelRemaining_map_headActionReward
            policy remaining hremaining state]
    _ = policy.actionKernel
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
          rw [source.actionRewardKernel_map_fst]

/-- Under the one-step joint law, reward conditioned on action is the selected reward kernel. -/
theorem actionRewardKernel_condDistrib_reward_given_action
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    (state : State) :
    ProbabilityTheory.condDistrib Prod.snd Prod.fst
        (source.actionRewardKernel policy stage state) =ᵐ[
      (source.actionRewardKernel policy stage state).map Prod.fst]
      source.selectedRewardKernelAt state := by
  apply (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
    (μ := source.actionRewardKernel policy stage state)
    Prod.fst measurable_snd.aemeasurable
    (source.selectedRewardKernelAt state)).2
  rw [source.actionRewardKernel_map_fst]
  change
    (source.actionRewardKernel policy stage state).map id =
      policy.actionKernel stage state ⊗ₘ source.selectedRewardKernelAt state
  rw [Measure.map_id]
  exact source.actionRewardKernel_eq_compProd_selectedRewardKernelAt
    policy stage state

/-- On a generated positive trace, reward conditioned on the sampled head action has its selected law. -/
theorem stochasticTrajectoryKernelRemaining_condDistrib_headReward_given_headAction
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    ProbabilityTheory.condDistrib
        (RewardStepTrace.headReward
          (Action := Action) (State := State) remaining)
        (RewardStepTrace.headAction
          (Action := Action) (State := State) remaining)
        (source.stochasticTrajectoryKernelRemaining policy
          (remaining + 1) hremaining state) =ᵐ[
      (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state).map
        (RewardStepTrace.headAction
          (Action := Action) (State := State) remaining)]
      source.selectedRewardKernelAt state := by
  apply (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
    (μ := source.stochasticTrajectoryKernelRemaining policy
      (remaining + 1) hremaining state)
    (RewardStepTrace.headAction
      (Action := Action) (State := State) remaining)
    (RewardStepTrace.measurable_headReward remaining).aemeasurable
    (source.selectedRewardKernelAt state)).2
  rw [source.stochasticTrajectoryKernelRemaining_map_headAction
    policy remaining hremaining state]
  change
    (source.stochasticTrajectoryKernelRemaining policy
      (remaining + 1) hremaining state).map
        (RewardStepTrace.headActionReward
          (Action := Action) (State := State) remaining) =
      policy.actionKernel
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state ⊗ₘ
        source.selectedRewardKernelAt state
  rw [source.stochasticTrajectoryKernelRemaining_map_headActionReward
    policy remaining hremaining state]
  exact source.actionRewardKernel_eq_compProd_selectedRewardKernelAt
    policy _ state

/--
The generated head conditional law on `Real` is also the mapped conditional
expectation kernel on the sigma-algebra generated by the sampled head action.
-/
theorem stochasticTrajectoryKernelRemaining_condExpKernel_map_headReward_given_headAction
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    ∀ᵐ trace ∂
      (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state).trim
        (RewardStepTrace.measurable_headAction remaining).comap_le,
      Measure.map
          (RewardStepTrace.headReward
            (Action := Action) (State := State) remaining)
          (ProbabilityTheory.condExpKernel
            (source.stochasticTrajectoryKernelRemaining policy
              (remaining + 1) hremaining state)
            (MeasurableSpace.comap
              (RewardStepTrace.headAction
                (Action := Action) (State := State) remaining)
              inferInstance)
            trace) =
        source.selectedRewardKernelAt state
          (RewardStepTrace.headAction
            (Action := Action) (State := State) remaining trace) := by
  letI : Nonempty State := ⟨state⟩
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state)
      (RewardStepTrace.headReward
        (Action := Action) (State := State) remaining)
      (RewardStepTrace.headAction
        (Action := Action) (State := State) remaining)
      (RewardStepTrace.measurable_headReward remaining)
      (RewardStepTrace.measurable_headAction remaining)
      (source.selectedRewardKernelAt state)
      (source.stochasticTrajectoryKernelRemaining_condDistrib_headReward_given_headAction
        policy remaining hremaining state)

end MDP.MeanCompatibleRewardKernel
end FiniteHorizonRL
end BanditRLProof
