import BanditRLProof.RL.FiniteHorizonTrajectory
import BanditRLProof.RewardKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Stochastic reward kernels preserve finite-horizon mean planning

This module extends the finite-horizon MDP planning surface with a separate
Real reward kernel.  The compatibility contract says that every selected
reward is integrable and has the deterministic `mdp.reward` field as its mean.
The product with the transition kernel models conditional independence of the
reward and next state given the current state-action pair.

The resulting one-step, policy, and backward stochastic Bellman values equal
the existing mean-reward definitions.  This is a planning transport theorem;
it does not construct a stochastic-reward trajectory law or a concentration
bound.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace MDP

/--
A stochastic Real reward kernel whose selected rewards are integrable and
have the mean stored in the finite-horizon MDP reward field.
-/
structure MeanCompatibleRewardKernel (mdp : MDP State Action) where
  rewardKernel : RewardKernel.MarkovRewardKernel (Prod State Action) Real
  integrable_reward : forall state action,
    Integrable (fun reward : Real => reward)
      (rewardKernel.kernel (state, action))
  integral_reward_eq : forall state action,
    integral (rewardKernel.kernel (state, action))
        (fun reward : Real => reward) =
      mdp.reward state action

namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- The conditionally independent joint law of reward and next state. -/
noncomputable def rewardNextStateKernel
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.Kernel (Prod State Action) (Prod Real State) :=
  ProbabilityTheory.Kernel.prod source.rewardKernel.kernel mdp.transition

instance instRewardNextStateKernelIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.IsMarkovKernel source.rewardNextStateKernel := by
  unfold rewardNextStateKernel
  infer_instance

/-- Expected sampled reward plus continuation value under the joint kernel. -/
noncomputable def stochasticBellmanQ
    (source : MeanCompatibleRewardKernel mdp)
    (value : State -> Real) (state : State) (action : Action) : Real :=
  integral (source.rewardNextStateKernel (state, action))
    (fun pair : Prod Real State => pair.1 + value pair.2)

/-- The sampled one-step return is integrable for measurable continuation values. -/
theorem integrable_reward_add_value
    (source : MeanCompatibleRewardKernel mdp)
    {value : State -> Real} (hvalue : Measurable value)
    (state : State) (action : Action) :
    Integrable (fun pair : Prod Real State => pair.1 + value pair.2)
      (source.rewardNextStateKernel (state, action)) := by
  haveI : IsProbabilityMeasure
      (source.rewardKernel.kernel (state, action)) :=
    RewardKernel.isProbabilityMeasure_apply source.rewardKernel (state, action)
  haveI : IsProbabilityMeasure (mdp.transition (state, action)) := by
    infer_instance
  rw [rewardNextStateKernel, ProbabilityTheory.Kernel.prod_apply]
  exact
    (source.integrable_reward state action).comp_fst
        (mdp.transition (state, action)) |>.add
      ((integrable_of_fintype (mdp.transition (state, action)) value hvalue).comp_snd
        (source.rewardKernel.kernel (state, action)))

/-- Sampling a mean-compatible reward preserves the existing Bellman action value. -/
theorem stochasticBellmanQ_eq_bellmanQ
    (source : MeanCompatibleRewardKernel mdp)
    {value : State -> Real} (hvalue : Measurable value)
    (state : State) (action : Action) :
    source.stochasticBellmanQ value state action =
      mdp.bellmanQ value state action := by
  haveI : IsProbabilityMeasure
      (source.rewardKernel.kernel (state, action)) :=
    RewardKernel.isProbabilityMeasure_apply source.rewardKernel (state, action)
  haveI : IsProbabilityMeasure (mdp.transition (state, action)) := by
    infer_instance
  have hreward := source.integrable_reward state action
  have hnext :=
    integrable_of_fintype (mdp.transition (state, action)) value hvalue
  have hjoint :
      Integrable (fun pair : Prod Real State => pair.1 + value pair.2)
        ((source.rewardKernel.kernel (state, action)).prod
          (mdp.transition (state, action))) :=
    (hreward.comp_fst (mdp.transition (state, action))).add
      (hnext.comp_snd (source.rewardKernel.kernel (state, action)))
  rw [stochasticBellmanQ, rewardNextStateKernel,
    ProbabilityTheory.Kernel.prod_apply]
  rw [integral_prod _ hjoint]
  have hinner (reward : Real) :
      integral (mdp.transition (state, action))
          (fun nextState => reward + value nextState) =
        reward + mdp.transitionValue value state action := by
    rw [integral_add (integrable_const _) hnext]
    simp [MDP.transitionValue]
  simp_rw [hinner]
  rw [integral_add hreward (integrable_const _)]
  simp [source.integral_reward_eq, MDP.bellmanQ, MDP.transitionValue]

/-- Policy expectation formed from the sampled stochastic Bellman action value. -/
noncomputable def stochasticBellman
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    (value : State -> Real) (state : State) : Real :=
  integral (policy.actionKernel stage state)
    (fun action => source.stochasticBellmanQ value state action)

/-- The stochastic policy Bellman operator equals the existing mean operator. -/
theorem stochasticBellman_eq_bellman
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    {value : State -> Real} (hvalue : Measurable value) :
    source.stochasticBellman policy stage value =
      policy.bellman stage value := by
  funext state
  unfold stochasticBellman MarkovPolicy.bellman
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun action =>
    source.stochasticBellmanQ_eq_bellmanQ hvalue state action

/-- Backward policy value computed with sampled stochastic reward laws. -/
noncomputable def stochasticValueRemaining
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State -> Real
  | 0, _ => fun _ => 0
  | remaining + 1, hremaining =>
      source.stochasticBellman policy
        ⟨mdp.horizon - (remaining + 1), by omega⟩
        (source.stochasticValueRemaining policy remaining (by omega))

/-- Stochastic backward policy evaluation equals mean-reward evaluation. -/
theorem stochasticValueRemaining_eq_valueRemaining
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    source.stochasticValueRemaining policy remaining hremaining =
      policy.valueRemaining remaining hremaining := by
  induction remaining with
  | zero =>
      rfl
  | succ remaining ih =>
      rw [stochasticValueRemaining, MarkovPolicy.valueRemaining]
      rw [source.stochasticBellman_eq_bellman]
      · congr 1
        exact ih (by omega)
      · rw [ih (by omega)]
        exact policy.measurable_valueRemaining remaining (by omega)

/-- Stochastic policy value at a chronological stage. -/
noncomputable def stochasticValueAt
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (stage : Nat) (_hstage : stage <= mdp.horizon) : State -> Real :=
  source.stochasticValueRemaining policy
    (mdp.horizon - stage) (Nat.sub_le _ _)

/-- Every chronological stochastic value equals the existing policy value. -/
theorem stochasticValueAt_eq_valueAt
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (stage : Nat) (hstage : stage <= mdp.horizon) :
    source.stochasticValueAt policy stage hstage =
      policy.valueAt stage hstage := by
  exact source.stochasticValueRemaining_eq_valueRemaining policy _ _

/-- The deterministic MDP reward, viewed as a kernel, is mean-compatible. -/
noncomputable def deterministic (mdp : MDP State Action) :
    MeanCompatibleRewardKernel mdp where
  rewardKernel := RewardKernel.deterministic
    (Function.uncurry mdp.reward) mdp.measurable_reward
  integrable_reward := by
    intro state action
    rw [RewardKernel.deterministic,
      ProbabilityTheory.Kernel.deterministic_apply]
    exact integrable_dirac' measurable_id.stronglyMeasurable (by simp)
  integral_reward_eq := by
    intro state action
    rw [RewardKernel.deterministic,
      ProbabilityTheory.Kernel.deterministic_apply]
    exact integral_dirac' (fun reward : Real => reward)
      (mdp.reward state action) measurable_id.stronglyMeasurable

/--
Terminal mean-planning transport: the product kernel is Markov and all sampled
Bellman and backward values agree with the existing deterministic-mean model.
-/
theorem meanPlanningTransport
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) :
    ProbabilityTheory.IsMarkovKernel source.rewardNextStateKernel ∧
    (forall (value : State -> Real), Measurable value ->
      forall state action,
        source.stochasticBellmanQ value state action =
          mdp.bellmanQ value state action) ∧
    (forall (stage : Fin mdp.horizon) (value : State -> Real),
      Measurable value ->
        source.stochasticBellman policy stage value =
          policy.bellman stage value) ∧
    (forall (remaining : Nat) (hremaining : remaining <= mdp.horizon),
      source.stochasticValueRemaining policy remaining hremaining =
        policy.valueRemaining remaining hremaining) ∧
    (forall (stage : Nat) (hstage : stage <= mdp.horizon),
      source.stochasticValueAt policy stage hstage =
        policy.valueAt stage hstage) := by
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro value hvalue state action
    exact source.stochasticBellmanQ_eq_bellmanQ hvalue state action
  · intro stage value hvalue
    exact source.stochasticBellman_eq_bellman policy stage hvalue
  · intro remaining hremaining
    exact source.stochasticValueRemaining_eq_valueRemaining policy remaining hremaining
  · intro stage hstage
    exact source.stochasticValueAt_eq_valueAt policy stage hstage

end MeanCompatibleRewardKernel
end MDP
end FiniteHorizonRL
end BanditRLProof
