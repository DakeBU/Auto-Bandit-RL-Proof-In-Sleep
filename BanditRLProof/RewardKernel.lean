import BanditRLProof.PolicyMeasurability
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Moments.SubGaussian

/-!
# Reward kernel contract surface

This module records a narrow `KERNEL-REWARD` leaf: a reward law is represented
as a Mathlib Markov kernel indexed by an arm/context object.  It exposes the
kernel and the measurability/probability regularity facts needed by later
policy-kernel and trajectory-law leaves, but it does not bind kernels or build
a trajectory measure.
-/

open MeasureTheory

universe u v w x y

namespace BanditRLProof
namespace RewardKernel

/--
A reward distribution indexed by an arm/context object.  The underlying object
is Mathlib's `ProbabilityTheory.Kernel`; the local wrapper gives later bandit
proof leaves a stable project-level name for the regularity contract.
-/
structure MarkovRewardKernel
    (Index : Type u) (Reward : Type v)
    [MeasurableSpace Index] [MeasurableSpace Reward] where
  kernel : ProbabilityTheory.Kernel Index Reward
  isMarkovKernel : ProbabilityTheory.IsMarkovKernel kernel

variable {Index : Type u} {Reward : Type v}
    [MeasurableSpace Index] [MeasurableSpace Reward]

instance instIsMarkovKernel
    (rewardKernel : MarkovRewardKernel Index Reward) :
    ProbabilityTheory.IsMarkovKernel rewardKernel.kernel :=
  rewardKernel.isMarkovKernel

/-- Build the local reward-kernel contract from a Mathlib Markov kernel. -/
def ofKernel
    (kernel : ProbabilityTheory.Kernel Index Reward)
    (hkernel : ProbabilityTheory.IsMarkovKernel kernel) :
    MarkovRewardKernel Index Reward where
  kernel := kernel
  isMarkovKernel := hkernel

/-- The reward kernel is measurable as a map into measures. -/
theorem measurable_kernel
    (rewardKernel : MarkovRewardKernel Index Reward) :
    Measurable rewardKernel.kernel :=
  rewardKernel.kernel.measurable

/-- A measurable random index selects a measurable random reward measure. -/
theorem measurable_apply_of_measurable_index
    {Omega : Type w} [MeasurableSpace Omega]
    (rewardKernel : MarkovRewardKernel Index Reward)
    (index : Omega -> Index)
    (hindex : Measurable index) :
    Measurable (fun omega : Omega => rewardKernel.kernel (index omega)) :=
  rewardKernel.kernel.measurable.comp hindex

/--
For every measurable reward event, the selected event probability is a
measurable scalar function of the random index.
-/
theorem measurable_eventProbability_of_measurable_index
    {Omega : Type w} [MeasurableSpace Omega]
    (rewardKernel : MarkovRewardKernel Index Reward)
    (index : Omega -> Index)
    (hindex : Measurable index)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega => rewardKernel.kernel (index omega) event) :=
  (ProbabilityTheory.Kernel.measurable_coe rewardKernel.kernel hevent).comp
    hindex

/-- Every measure selected by a reward kernel is a probability measure. -/
theorem isProbabilityMeasure_apply
    (rewardKernel : MarkovRewardKernel Index Reward)
    (index : Index) :
    IsProbabilityMeasure (rewardKernel.kernel index) := by
  haveI : ProbabilityTheory.IsMarkovKernel rewardKernel.kernel :=
    rewardKernel.isMarkovKernel
  infer_instance

@[simp]
theorem apply_univ
    (rewardKernel : MarkovRewardKernel Index Reward)
    (index : Index) :
    rewardKernel.kernel index Set.univ = 1 := by
  haveI : IsProbabilityMeasure (rewardKernel.kernel index) :=
    isProbabilityMeasure_apply rewardKernel index
  simp

/-- Constant probability reward law as a reward-kernel contract. -/
def const
    (mu : Measure Reward)
    (hmu : IsProbabilityMeasure mu) :
    MarkovRewardKernel Index Reward where
  kernel := ProbabilityTheory.Kernel.const Index mu
  isMarkovKernel := by
    haveI : IsProbabilityMeasure mu := hmu
    infer_instance

/-- Deterministic measurable reward law as a reward-kernel contract. -/
noncomputable def deterministic
    (reward : Index -> Reward)
    (hreward : Measurable reward) :
    MarkovRewardKernel Index Reward where
  kernel := ProbabilityTheory.Kernel.deterministic reward hreward
  isMarkovKernel := by infer_instance

variable {Context : Type x} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace Action]

/--
Select the reward measure associated with a context/action pair.  This is only
the one-step reward-law lookup; it is not a trajectory-law construction.
-/
def selectedMeasure
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (context : Context) (action : Action) :
    Measure Reward :=
  rewardKernel.kernel (context, action)

/-- A context/action-selected reward measure is a probability measure. -/
theorem isProbabilityMeasure_selectedMeasure
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (context : Context) (action : Action) :
    IsProbabilityMeasure
      (selectedMeasure rewardKernel context action) := by
  simpa [selectedMeasure] using
    isProbabilityMeasure_apply rewardKernel (context, action)

@[simp]
theorem selectedMeasure_univ
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (context : Context) (action : Action) :
    selectedMeasure rewardKernel context action Set.univ = 1 := by
  simp [selectedMeasure]

/--
Measurable context and action random variables select a measurable random
reward measure from the context/action reward kernel.
-/
theorem measurable_selectedMeasure_of_measurable
    {Omega : Type w} [MeasurableSpace Omega]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (context : Omega -> Context)
    (action : Omega -> Action)
    (hcontext : Measurable context)
    (haction : Measurable action) :
    Measurable
      (fun omega : Omega =>
        selectedMeasure rewardKernel (context omega) (action omega)) := by
  exact
    measurable_apply_of_measurable_index rewardKernel
      (fun omega : Omega => (context omega, action omega))
      (hcontext.prod haction)

/--
For a measurable reward event, measurable context and action random variables
select a measurable event-probability scalar from the reward kernel.
-/
theorem measurable_selectedEventProbability_of_measurable
    {Omega : Type w} [MeasurableSpace Omega]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (context : Omega -> Context)
    (action : Omega -> Action)
    (hcontext : Measurable context)
    (haction : Measurable action)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega =>
        selectedMeasure rewardKernel (context omega) (action omega) event) := by
  exact
    measurable_eventProbability_of_measurable_index rewardKernel
      (fun omega : Omega => (context omega, action omega))
      (hcontext.prod haction)
      hevent

/--
A measurable policy applied to a measurable state can be used as the action
coordinate of a context/action reward kernel.
-/
theorem measurable_selectedMeasure_of_policy_state
    {Omega : Type w} {State : Type u}
    [MeasurableSpace Omega] [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (context : Omega -> Context)
    (state : Omega -> State)
    (hcontext : Measurable context)
    (hstate : Measurable state) :
    Measurable
      (fun omega : Omega =>
        selectedMeasure rewardKernel (context omega)
          (policy.action (state omega))) := by
  exact
    measurable_selectedMeasure_of_measurable rewardKernel context
      (fun omega : Omega => policy.action (state omega))
      hcontext
      (Policy.measurable_action_of_measurable_state policy state hstate)

/--
Event-probability version of
`measurable_selectedMeasure_of_policy_state`.
-/
theorem measurable_selectedEventProbability_of_policy_state
    {Omega : Type w} {State : Type u}
    [MeasurableSpace Omega] [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (context : Omega -> Context)
    (state : Omega -> State)
    (hcontext : Measurable context)
    (hstate : Measurable state)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega =>
        selectedMeasure rewardKernel (context omega)
          (policy.action (state omega)) event) := by
  exact
    measurable_selectedEventProbability_of_measurable rewardKernel context
      (fun omega : Omega => policy.action (state omega))
      hcontext
      (Policy.measurable_action_of_measurable_state policy state hstate)
      hevent

/--
The deterministic index map that turns a context/state pair into the
context/action pair selected by a measurable policy.
-/
def policyContextStateIndex
    {State : Type u} [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    Context × State -> Context × Action :=
  fun pair => (pair.1, policy.action pair.2)

/-- The policy-induced context/state index map is measurable. -/
theorem measurable_policyContextStateIndex
    {State : Type u} [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    Measurable (policyContextStateIndex (Context := Context) policy) := by
  exact measurable_fst.prodMk (policy.measurable_action.comp measurable_snd)

/--
Compose a measurable policy with a context/action reward kernel to obtain the
one-step reward kernel indexed by context/state pairs.

This is a one-step `KERNEL-POLICY-BIND` precursor.  It composes the policy map
with reward-kernel lookup, but it does not yet build a finite-horizon or
infinite-horizon trajectory law.
-/
def composePolicy
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    MarkovRewardKernel (Context × State) Reward where
  kernel :=
    { toFun := fun pair : Context × State =>
        selectedMeasure rewardKernel pair.1 (policy.action pair.2)
      measurable' := by
        simpa [policyContextStateIndex, selectedMeasure] using
          measurable_apply_of_measurable_index rewardKernel
            (policyContextStateIndex (Context := Context) policy)
            (measurable_policyContextStateIndex
              (Context := Context) policy) }
  isMarkovKernel := by
    refine ⟨fun pair => ?_⟩
    simpa [selectedMeasure] using
      isProbabilityMeasure_selectedMeasure rewardKernel pair.1
        (policy.action pair.2)

@[simp]
theorem composePolicy_kernel_apply
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    (composePolicy rewardKernel policy).kernel pair =
      selectedMeasure rewardKernel pair.1 (policy.action pair.2) :=
  rfl

/-- The composed policy/reward kernel is a Mathlib Markov kernel. -/
theorem isMarkovKernel_composePolicy
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.IsMarkovKernel
      (composePolicy rewardKernel policy).kernel :=
  (composePolicy rewardKernel policy).isMarkovKernel

/--
For a measurable reward event, the event probability under the composed
policy/reward kernel is measurable in the context/state pair.
-/
theorem measurable_composePolicy_eventProbability
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun pair : Context × State =>
        (composePolicy rewardKernel policy).kernel pair event) := by
  exact
    measurable_eventProbability_of_measurable_index
      (composePolicy rewardKernel policy)
      (fun pair : Context × State => pair)
      measurable_id
      hevent

/--
The policy-selected action as a deterministic map from context/state pairs.
The context coordinate is carried so this map has the same source as the
composed context/state reward kernel.
-/
def policyActionOfContextState
    {State : Type u} [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    Context × State -> Action :=
  fun pair => policy.action pair.2

/-- The policy-selected action map on context/state pairs is measurable. -/
theorem measurable_policyActionOfContextState
    {State : Type u} [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    Measurable (policyActionOfContextState (Context := Context) policy) := by
  exact policy.measurable_action.comp measurable_snd

/-- The deterministic action kernel induced by a measurable policy. -/
noncomputable def policyActionKernel
    {State : Type u} [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.Kernel (Context × State) Action :=
  ProbabilityTheory.Kernel.deterministic
    (policyActionOfContextState (Context := Context) policy)
    (measurable_policyActionOfContextState (Context := Context) policy)

@[simp]
theorem policyActionKernel_apply
    {State : Type u} [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    policyActionKernel (Context := Context) policy pair =
      Measure.dirac (policy.action pair.2) :=
  rfl

/-- The policy action kernel is a Mathlib Markov kernel. -/
theorem isMarkovKernel_policyActionKernel
    {State : Type u} [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.IsMarkovKernel
      (policyActionKernel (Context := Context) policy) := by
  unfold policyActionKernel
  infer_instance

/--
One-step action/reward kernel induced by a deterministic measurable policy and
a context/action reward kernel.

The output is the pair `(action, reward)`: the action coordinate is the
policy-selected deterministic action, and the reward coordinate is drawn from
the reward law selected by that same action.  This is still a one-step
construction; finite-prefix assembly is provided separately below.
-/
noncomputable def composePolicyActionReward
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    MarkovRewardKernel (Context × State) (Action × Reward) where
  kernel :=
    ProbabilityTheory.Kernel.prod
      (policyActionKernel (Context := Context) policy)
      (composePolicy rewardKernel policy).kernel
  isMarkovKernel := by
    haveI :
        ProbabilityTheory.IsMarkovKernel
          (policyActionKernel (Context := Context) policy) :=
      isMarkovKernel_policyActionKernel (Context := Context) policy
    haveI :
        ProbabilityTheory.IsMarkovKernel
          (composePolicy rewardKernel policy).kernel :=
      isMarkovKernel_composePolicy rewardKernel policy
    infer_instance

@[simp]
theorem composePolicyActionReward_kernel
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    (composePolicyActionReward rewardKernel policy).kernel =
      ProbabilityTheory.Kernel.prod
        (policyActionKernel (Context := Context) policy)
        (composePolicy rewardKernel policy).kernel :=
  rfl

/-- The one-step action/reward policy/reward kernel is a Mathlib Markov kernel. -/
theorem isMarkovKernel_composePolicyActionReward
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.IsMarkovKernel
      (composePolicyActionReward rewardKernel policy).kernel :=
  (composePolicyActionReward rewardKernel policy).isMarkovKernel

/--
Event-probability measurability for the one-step action/reward kernel.
-/
theorem measurable_composePolicyActionReward_eventProbability
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    {event : Set (Action × Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun pair : Context × State =>
        (composePolicyActionReward rewardKernel policy).kernel pair event) := by
  exact
    measurable_eventProbability_of_measurable_index
      (composePolicyActionReward rewardKernel policy)
      (fun pair : Context × State => pair)
      measurable_id
      hevent

/--
The reward marginal of the one-step action/reward kernel is exactly the
policy-selected reward law.

This is a kernel-level law-transfer wrapper: it identifies the second
coordinate of the `(Action × Reward)` step kernel, but it does not identify a
global conditional expectation kernel.
-/
theorem composePolicyActionReward_reward_event
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    (composePolicyActionReward rewardKernel policy).kernel pair
        (Prod.snd ⁻¹' event) =
      selectedMeasure rewardKernel pair.1 (policy.action pair.2) event := by
  have hsnd :
      ProbabilityTheory.Kernel.snd
        (composePolicyActionReward rewardKernel policy).kernel =
      (composePolicy rewardKernel policy).kernel := by
    rw [composePolicyActionReward_kernel]
    haveI :
        ProbabilityTheory.IsMarkovKernel
          (policyActionKernel (Context := Context) policy) :=
      isMarkovKernel_policyActionKernel (Context := Context) policy
    haveI :
        ProbabilityTheory.IsSFiniteKernel
          (composePolicy rewardKernel policy).kernel := by
      infer_instance
    exact
      ProbabilityTheory.Kernel.snd_prod
        (policyActionKernel (Context := Context) policy)
        (composePolicy rewardKernel policy).kernel
  calc
    (composePolicyActionReward rewardKernel policy).kernel pair
        (Prod.snd ⁻¹' event)
        =
      ProbabilityTheory.Kernel.snd
        (composePolicyActionReward rewardKernel policy).kernel pair event := by
          rw [ProbabilityTheory.Kernel.snd_apply'
            (composePolicyActionReward rewardKernel policy).kernel pair hevent]
    _ = (composePolicy rewardKernel policy).kernel pair event := by
          rw [hsnd]
    _ = selectedMeasure rewardKernel pair.1 (policy.action pair.2) event := by
          rw [composePolicy_kernel_apply]

/--
Measure-level reward marginal of the one-step action/reward kernel.

This is the pushforward version of `composePolicyActionReward_reward_event`.
It exposes the exact shape needed by conditional-kernel law identification:
mapping the `(Action × Reward)` one-step law through `Prod.snd` recovers the
policy-selected reward law.
-/
theorem composePolicyActionReward_reward_map
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    Measure.map Prod.snd
        ((composePolicyActionReward rewardKernel policy).kernel pair) =
      selectedMeasure rewardKernel pair.1 (policy.action pair.2) := by
  refine Measure.ext fun event hevent => ?_
  rw [Measure.map_apply measurable_snd hevent]
  exact
    composePolicyActionReward_reward_event rewardKernel policy pair hevent

/--
Pointwise measure shape of the one-step action/reward policy/reward kernel.

The action coordinate is deterministic, so the full `(Action × Reward)` law is
the selected reward law pushed through `Prod.mk` with the policy action fixed.
-/
theorem composePolicyActionReward_kernel_apply_eq_map_prod_mk
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    (composePolicyActionReward rewardKernel policy).kernel pair =
      Measure.map (Prod.mk (policy.action pair.2))
        (selectedMeasure rewardKernel pair.1 (policy.action pair.2)) := by
  haveI :
      ProbabilityTheory.IsMarkovKernel
        (policyActionKernel (Context := Context) policy) :=
    isMarkovKernel_policyActionKernel (Context := Context) policy
  haveI :
      ProbabilityTheory.IsSFiniteKernel
        (composePolicy rewardKernel policy).kernel := by
    infer_instance
  haveI :
      IsProbabilityMeasure
        (selectedMeasure rewardKernel pair.1 (policy.action pair.2)) :=
    isProbabilityMeasure_selectedMeasure rewardKernel pair.1
      (policy.action pair.2)
  rw [composePolicyActionReward_kernel]
  rw [ProbabilityTheory.Kernel.prod_apply]
  rw [policyActionKernel_apply]
  rw [composePolicy_kernel_apply]
  rw [Measure.dirac_prod]

/--
Pointwise centered-reward law contract for a context/action reward kernel.

For every context/action index, the selected reward law has a centered reward
with zero integral and a sub-Gaussian MGF.  The contract is deliberately
one-step: the transfer theorems below move these facts through policy
composition and history-indexed step kernels, but they do not identify a
global trajectory conditional expectation.
-/
structure CenteredRewardKernelLaw
    {Context : Type x} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal) where
  integrable :
    forall context action,
      MeasureTheory.Integrable
        (fun reward : Rat =>
          (((reward - mean context action : Rat) : Real)))
        (selectedMeasure rewardKernel context action)
  integral_eq_zero :
    forall context action,
      MeasureTheory.integral (selectedMeasure rewardKernel context action)
        (fun reward : Rat =>
          (((reward - mean context action : Rat) : Real))) = 0
  hasSubgaussianMGF :
    forall context action,
      ProbabilityTheory.HasSubgaussianMGF
        (fun reward : Rat =>
          (((reward - mean context action : Rat) : Real)))
        (varianceProxy context action)
        (selectedMeasure rewardKernel context action)

/--
A policy-composed one-step reward kernel inherits centered-reward integrability
from the underlying context/action reward law.
-/
theorem composePolicy_centeredReward_integrable
    {Context : Type x} {State : Type u} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (policy : Policy.MeasurablePolicy State Action)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (pair : Context × State) :
    MeasureTheory.Integrable
      (fun reward : Rat =>
        (((reward - mean pair.1 (policy.action pair.2) : Rat) : Real)))
      ((composePolicy rewardKernel policy).kernel pair) := by
  simpa using
    law.integrable pair.1 (policy.action pair.2)

/--
A policy-composed one-step reward kernel inherits the centered-reward
zero-integral fact from the underlying context/action reward law.
-/
theorem composePolicy_centeredReward_integral_eq_zero
    {Context : Type x} {State : Type u} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (policy : Policy.MeasurablePolicy State Action)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (pair : Context × State) :
    MeasureTheory.integral ((composePolicy rewardKernel policy).kernel pair)
      (fun reward : Rat =>
        (((reward - mean pair.1 (policy.action pair.2) : Rat) : Real))) = 0 := by
  simpa using
    law.integral_eq_zero pair.1 (policy.action pair.2)

/--
A policy-composed one-step reward kernel inherits the centered-reward
sub-Gaussian MGF witness from the underlying context/action reward law.
-/
theorem composePolicy_centeredReward_hasSubgaussianMGF
    {Context : Type x} {State : Type u} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (policy : Policy.MeasurablePolicy State Action)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (pair : Context × State) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        (((reward - mean pair.1 (policy.action pair.2) : Rat) : Real)))
      (varianceProxy pair.1 (policy.action pair.2))
      ((composePolicy rewardKernel policy).kernel pair) := by
  simpa using
    law.hasSubgaussianMGF pair.1 (policy.action pair.2)

/--
The one-step reward kernel selected from a finite reward history.

This is an Ionescu-Tulcea-facing precursor for `KERNEL-POLICY-BIND`: for each
time `n`, a measurable context extractor and a measurable policy-state
extractor turn the finite reward history `Π i : Finset.Iic n, Reward` into the
context/state pair consumed by the one-step policy/reward kernel.
-/
def historyStepRewardKernel
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    MarkovRewardKernel ((i : Finset.Iic n) -> Reward) Reward where
  kernel :=
    { toFun := fun history =>
        selectedMeasure rewardKernel (context n history)
          ((policy n).action (state n history))
      measurable' := by
        exact
          measurable_selectedMeasure_of_policy_state rewardKernel (policy n)
            (context n) (state n) (hcontext n) (hstate n) }
  isMarkovKernel := by
    refine ⟨fun history => ?_⟩
    simpa [selectedMeasure] using
      isProbabilityMeasure_selectedMeasure rewardKernel (context n history)
        ((policy n).action (state n history))

/--
The Mathlib kernel family consumed by `ProbabilityTheory.Kernel.partialTraj`
for the constant reward-coordinate type family.
-/
def historyStepKernelFamily
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n)) :
    (n : Nat) ->
      ProbabilityTheory.Kernel ((i : Finset.Iic n) -> Reward) Reward :=
  fun n =>
    (historyStepRewardKernel rewardKernel policy context state hcontext hstate n).kernel

@[simp]
theorem historyStepKernelFamily_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Reward) :
    historyStepKernelFamily rewardKernel policy context state hcontext hstate n history =
      selectedMeasure rewardKernel (context n history)
        ((policy n).action (state n history)) :=
  rfl

/-- Every kernel in `historyStepKernelFamily` is a Mathlib Markov kernel. -/
theorem isMarkovKernel_historyStepKernelFamily
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n)) :
    forall n : Nat,
      ProbabilityTheory.IsMarkovKernel
        (historyStepKernelFamily rewardKernel policy context state hcontext hstate n) :=
  fun n =>
    (historyStepRewardKernel rewardKernel policy context state hcontext hstate n).isMarkovKernel

/--
For any measurable reward event, the event probability selected by one member
of the history-indexed kernel family is measurable in the finite reward
history.
-/
theorem measurable_historyStepKernelFamily_eventProbability
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic n) -> Reward =>
        historyStepKernelFamily rewardKernel policy context state hcontext hstate
          n history event) := by
  exact
    measurable_selectedEventProbability_of_policy_state rewardKernel (policy n)
      (context n) (state n) (hcontext n) (hstate n) hevent

/--
The history-indexed one-step reward kernel inherits centered-reward
integrability from the underlying context/action reward law.
-/
theorem historyStepKernelFamily_centeredReward_integrable
    {Context : Type x} {State : Type u} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat) (history : (i : Finset.Iic n) -> Rat) :
    MeasureTheory.Integrable
      (fun reward : Rat =>
        (((reward -
          mean (context n history) ((policy n).action (state n history)) :
            Rat) : Real)))
      (historyStepKernelFamily rewardKernel policy context state hcontext hstate
        n history) := by
  simpa [historyStepKernelFamily_apply] using
    law.integrable (context n history) ((policy n).action (state n history))

/--
The history-indexed one-step reward kernel inherits the centered-reward
zero-integral fact from the underlying context/action reward law.
-/
theorem historyStepKernelFamily_centeredReward_integral_eq_zero
    {Context : Type x} {State : Type u} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat) (history : (i : Finset.Iic n) -> Rat) :
    MeasureTheory.integral
      (historyStepKernelFamily rewardKernel policy context state hcontext hstate
        n history)
      (fun reward : Rat =>
        (((reward -
          mean (context n history) ((policy n).action (state n history)) :
            Rat) : Real))) = 0 := by
  simpa [historyStepKernelFamily_apply] using
    law.integral_eq_zero
      (context n history) ((policy n).action (state n history))

/--
The history-indexed one-step reward kernel inherits the centered-reward
sub-Gaussian MGF witness from the underlying context/action reward law.
-/
theorem historyStepKernelFamily_centeredReward_hasSubgaussianMGF
    {Context : Type x} {State : Type u} {Action : Type y}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat) (history : (i : Finset.Iic n) -> Rat) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        (((reward -
          mean (context n history) ((policy n).action (state n history)) :
            Rat) : Real)))
      (varianceProxy
        (context n history) ((policy n).action (state n history)))
      (historyStepKernelFamily rewardKernel policy context state hcontext hstate
        n history) := by
  simpa [historyStepKernelFamily_apply] using
    law.hasSubgaussianMGF
      (context n history) ((policy n).action (state n history))

/--
Finite-prefix trajectory kernel obtained by feeding the history-indexed
policy/reward step-kernel family to Mathlib's `partialTraj` construction.

This gives the finite-prefix Ionescu-Tulcea assembly surface for reward
histories only.  It is not yet the final bandit trajectory law with action
trace, conditional reward-law transfer, or adaptive regret theorem.
-/
noncomputable def partialTrajectoryKernel
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.Kernel
      ((i : Finset.Iic a) -> Reward)
      ((i : Finset.Iic b) -> Reward) :=
  ProbabilityTheory.Kernel.partialTraj
    (X := fun _ : Nat => Reward)
    (historyStepKernelFamily rewardKernel policy context state hcontext hstate)
    a b

/-- The finite-prefix trajectory kernel assembled by `partialTraj` is Markov. -/
theorem isMarkovKernel_partialTrajectoryKernel
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (partialTrajectoryKernel rewardKernel policy context state hcontext hstate
        a b) := by
  haveI :
      forall n : Nat,
        ProbabilityTheory.IsMarkovKernel
          (historyStepKernelFamily rewardKernel policy context state hcontext hstate n) :=
    isMarkovKernel_historyStepKernelFamily rewardKernel policy context state
      hcontext hstate
  unfold partialTrajectoryKernel
  infer_instance

/--
Event-probability measurability for the finite-prefix trajectory kernel
assembled by Mathlib's `partialTraj`.
-/
theorem measurable_partialTrajectoryKernel_eventProbability
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat)
    {event : Set ((i : Finset.Iic b) -> Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic a) -> Reward =>
        partialTrajectoryKernel rewardKernel policy context state hcontext hstate
          a b history event) := by
  exact
    ProbabilityTheory.Kernel.measurable_coe
      (partialTrajectoryKernel rewardKernel policy context state hcontext hstate
        a b)
      hevent

/--
For a one-step extension, the reward-only partial trajectory kernel has the
configured history-step reward kernel as its next-coordinate marginal.

This is a local wrapper around Mathlib's `Kernel.map_partialTraj_succ_self`.
It is a trajectory-kernel fact, not a conditional-expectation-kernel
identification.
-/
theorem partialTrajectoryKernel_succ_next_map
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    (partialTrajectoryKernel rewardKernel policy context state hcontext hstate
        n (n + 1)).map
      (fun history : (i : Finset.Iic (n + 1)) -> Reward =>
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      historyStepKernelFamily rewardKernel policy context state hcontext hstate n := by
  haveI :
      forall n : Nat,
        ProbabilityTheory.IsMarkovKernel
          (historyStepKernelFamily rewardKernel policy context state hcontext hstate n) :=
    isMarkovKernel_historyStepKernelFamily rewardKernel policy context state
      hcontext hstate
  simpa [partialTrajectoryKernel] using
    (ProbabilityTheory.Kernel.map_partialTraj_succ_self
      (X := fun _ : Nat => Reward)
      (κ := historyStepKernelFamily rewardKernel policy context state hcontext hstate)
      n)

/--
Pointwise measure form of `partialTrajectoryKernel_succ_next_map`.
-/
theorem partialTrajectoryKernel_succ_next_map_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Reward) :
    Measure.map
        (fun extended : (i : Finset.Iic (n + 1)) -> Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
        (partialTrajectoryKernel rewardKernel policy context state hcontext hstate
          n (n + 1) history) =
      historyStepKernelFamily rewardKernel policy context state hcontext hstate
        n history := by
  have h_kernel :=
    partialTrajectoryKernel_succ_next_map rewardKernel policy context state
      hcontext hstate n
  have h_next_meas :
      Measurable
        (fun extended : (i : Finset.Iic (n + 1)) -> Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) :=
    measurable_pi_apply _
  simpa [ProbabilityTheory.Kernel.map_apply _ h_next_meas history] using
    congrArg (fun kernel => kernel history) h_kernel

/--
The one-step action/reward kernel selected from a finite action/reward pair
history.

This is the action/reward analogue of `historyStepRewardKernel`: the state
seen by the policy may depend on the finite prefix of previously emitted
`(Action × Reward)` pairs, and the next emitted object is again an
`(Action × Reward)` pair.
-/
noncomputable def actionRewardHistoryStepKernel
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    MarkovRewardKernel
      ((i : Finset.Iic n) -> Action × Reward) (Action × Reward) where
  kernel :=
    { toFun := fun history =>
        (composePolicyActionReward rewardKernel (policy n)).kernel
          (context n history, state n history)
      measurable' := by
        exact
          measurable_apply_of_measurable_index
            (composePolicyActionReward rewardKernel (policy n))
            (fun history => (context n history, state n history))
            ((hcontext n).prod (hstate n)) }
  isMarkovKernel := by
    refine ⟨fun history => ?_⟩
    exact
      isProbabilityMeasure_apply
        (composePolicyActionReward rewardKernel (policy n))
        (context n history, state n history)

/--
The Mathlib kernel family consumed by `partialTraj` for constant
`(Action × Reward)` trajectory coordinates.
-/
noncomputable def actionRewardHistoryStepKernelFamily
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n)) :
    (n : Nat) ->
      ProbabilityTheory.Kernel
        ((i : Finset.Iic n) -> Action × Reward) (Action × Reward) :=
  fun n =>
    (actionRewardHistoryStepKernel rewardKernel policy context state
      hcontext hstate n).kernel

@[simp]
theorem actionRewardHistoryStepKernelFamily_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    actionRewardHistoryStepKernelFamily rewardKernel policy context state
        hcontext hstate n history =
      (composePolicyActionReward rewardKernel (policy n)).kernel
        (context n history, state n history) :=
  rfl

/-- Every kernel in `actionRewardHistoryStepKernelFamily` is Markov. -/
theorem isMarkovKernel_actionRewardHistoryStepKernelFamily
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n)) :
    forall n : Nat,
      ProbabilityTheory.IsMarkovKernel
        (actionRewardHistoryStepKernelFamily rewardKernel policy context state
          hcontext hstate n) :=
  fun n =>
    (actionRewardHistoryStepKernel rewardKernel policy context state
      hcontext hstate n).isMarkovKernel

instance instIsMarkovKernel_actionRewardHistoryStepKernelFamily
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n)) :
    forall n : Nat,
      ProbabilityTheory.IsMarkovKernel
        (actionRewardHistoryStepKernelFamily rewardKernel policy context state
          hcontext hstate n) :=
  isMarkovKernel_actionRewardHistoryStepKernelFamily rewardKernel policy
    context state hcontext hstate

/--
For any measurable action/reward-pair event, the event probability selected by
one member of the action/reward history-indexed kernel family is measurable in
the finite action/reward pair history.
-/
theorem measurable_actionRewardHistoryStepKernelFamily_eventProbability
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat)
    {event : Set (Action × Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic n) -> Action × Reward =>
        actionRewardHistoryStepKernelFamily rewardKernel policy context state
          hcontext hstate n history event) := by
  exact
    measurable_eventProbability_of_measurable_index
      (composePolicyActionReward rewardKernel (policy n))
      (fun history => (context n history, state n history))
      ((hcontext n).prod (hstate n))
      hevent

/--
The reward marginal of a history-indexed one-step action/reward kernel is the
reward law selected by the same finite history.
-/
theorem actionRewardHistoryStepKernelFamily_reward_event
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    actionRewardHistoryStepKernelFamily rewardKernel policy context state
        hcontext hstate n history (Prod.snd ⁻¹' event) =
      selectedMeasure rewardKernel
        (context n history) ((policy n).action (state n history)) event := by
  rw [actionRewardHistoryStepKernelFamily_apply]
  exact
    composePolicyActionReward_reward_event rewardKernel (policy n)
      (context n history, state n history) hevent

/--
Measure-level reward marginal of a history-indexed one-step action/reward
kernel.

This is the pushforward version of
`actionRewardHistoryStepKernelFamily_reward_event`, and is the local
`RewardKernel` side of the future `condExpKernel` reward-coordinate map
identification.
-/
theorem actionRewardHistoryStepKernelFamily_reward_map
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    Measure.map Prod.snd
        (actionRewardHistoryStepKernelFamily rewardKernel policy context state
          hcontext hstate n history) =
      selectedMeasure rewardKernel
        (context n history) ((policy n).action (state n history)) := by
  refine Measure.ext fun event hevent => ?_
  rw [Measure.map_apply measurable_snd hevent]
  exact
    actionRewardHistoryStepKernelFamily_reward_event rewardKernel policy
      context state hcontext hstate n history hevent

/--
Pointwise measure shape of a history-indexed action/reward step kernel.

For a fixed finite pair history, the next action is the policy-selected action
and the reward coordinate is drawn from the corresponding selected reward law.
-/
theorem actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    actionRewardHistoryStepKernelFamily rewardKernel policy context state
        hcontext hstate n history =
      Measure.map
        (Prod.mk ((policy n).action (state n history)))
        (selectedMeasure rewardKernel (context n history)
          ((policy n).action (state n history))) := by
  rw [actionRewardHistoryStepKernelFamily_apply]
  exact
    composePolicyActionReward_kernel_apply_eq_map_prod_mk rewardKernel
      (policy n) (context n history, state n history)

/--
Finite-prefix action/reward trajectory kernel obtained by feeding the
history-indexed action/reward step-kernel family to Mathlib's `partialTraj`.

This is the compiled finite-prefix action/reward trajectory-law surface for
`KERNEL-POLICY-BIND`.  It still does not prove conditional reward-law transfer,
posterior kernels, or final adaptive regret theorems.
-/
noncomputable def actionRewardPartialTrajectoryKernel
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.Kernel
      ((i : Finset.Iic a) -> Action × Reward)
      ((i : Finset.Iic b) -> Action × Reward) :=
  ProbabilityTheory.Kernel.partialTraj
    (X := fun _ : Nat => Action × Reward)
    (actionRewardHistoryStepKernelFamily rewardKernel policy context state
      hcontext hstate)
    a b

/-- The finite-prefix action/reward trajectory kernel is Markov. -/
theorem isMarkovKernel_actionRewardPartialTrajectoryKernel
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (actionRewardPartialTrajectoryKernel rewardKernel policy context state
        hcontext hstate a b) := by
  haveI :
      forall n : Nat,
        ProbabilityTheory.IsMarkovKernel
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate n) :=
    isMarkovKernel_actionRewardHistoryStepKernelFamily rewardKernel policy
      context state hcontext hstate
  unfold actionRewardPartialTrajectoryKernel
  infer_instance

/--
Event-probability measurability for the finite-prefix action/reward trajectory
kernel assembled by Mathlib's `partialTraj`.
-/
theorem measurable_actionRewardPartialTrajectoryKernel_eventProbability
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat)
    {event : Set ((i : Finset.Iic b) -> Action × Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic a) -> Action × Reward =>
        actionRewardPartialTrajectoryKernel rewardKernel policy context state
          hcontext hstate a b history event) := by
  exact
    ProbabilityTheory.Kernel.measurable_coe
      (actionRewardPartialTrajectoryKernel rewardKernel policy context state
        hcontext hstate a b)
      hevent

/--
For a one-step extension, the action/reward partial trajectory kernel has the
configured action/reward history-step kernel as its next-coordinate marginal.

This is the action/reward-pair version of
`partialTrajectoryKernel_succ_next_map` and exposes the exact Mathlib
`partialTraj` marginal used by future `condExpKernel` pair-law identification.
-/
theorem actionRewardPartialTrajectoryKernel_succ_next_map
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    (actionRewardPartialTrajectoryKernel rewardKernel policy context state
        hcontext hstate n (n + 1)).map
      (fun history : (i : Finset.Iic (n + 1)) -> Action × Reward =>
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      actionRewardHistoryStepKernelFamily rewardKernel policy context state
        hcontext hstate n := by
  haveI :
      forall n : Nat,
        ProbabilityTheory.IsMarkovKernel
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate n) :=
    isMarkovKernel_actionRewardHistoryStepKernelFamily rewardKernel policy
      context state hcontext hstate
  simpa [actionRewardPartialTrajectoryKernel] using
    (ProbabilityTheory.Kernel.map_partialTraj_succ_self
      (X := fun _ : Nat => Action × Reward)
      (κ := actionRewardHistoryStepKernelFamily rewardKernel policy context state
        hcontext hstate)
      n)

/--
Pointwise measure form of
`actionRewardPartialTrajectoryKernel_succ_next_map`.
-/
theorem actionRewardPartialTrajectoryKernel_succ_next_map_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    Measure.map
        (fun extended : (i : Finset.Iic (n + 1)) -> Action × Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
        (actionRewardPartialTrajectoryKernel rewardKernel policy context state
          hcontext hstate n (n + 1) history) =
      actionRewardHistoryStepKernelFamily rewardKernel policy context state
        hcontext hstate n history := by
  have h_kernel :=
    actionRewardPartialTrajectoryKernel_succ_next_map rewardKernel policy
      context state hcontext hstate n
  have h_next_meas :
      Measurable
        (fun extended : (i : Finset.Iic (n + 1)) -> Action × Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) :=
    measurable_pi_apply _
  simpa [ProbabilityTheory.Kernel.map_apply _ h_next_meas history] using
    congrArg (fun kernel => kernel history) h_kernel

/--
Pointwise one-step extension form of the action/reward `partialTraj` kernel.

For one transition, the finite-prefix trajectory kernel is the history-step
action/reward kernel pushed through the deterministic operation that appends
the sampled next pair to the old finite pair prefix.
-/
theorem actionRewardPartialTrajectoryKernel_succ_extend_map_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    actionRewardPartialTrajectoryKernel rewardKernel policy context state
        hcontext hstate n (n + 1) history =
      Measure.map
        (fun next : Action × Reward =>
          History.extendPairHistorySucc history next)
        (actionRewardHistoryStepKernelFamily rewardKernel policy context state
          hcontext hstate n history) := by
  haveI :
      forall n : Nat,
        ProbabilityTheory.IsMarkovKernel
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate n) :=
    isMarkovKernel_actionRewardHistoryStepKernelFamily rewardKernel policy
      context state hcontext hstate
  have h_extend_comp :
      (fun next : Action × Reward =>
        IicProdIoc (X := fun _ : Nat => Action × Reward) n (n + 1)
          (history, MeasurableEquiv.piSingleton
            (X := fun _ : Nat => Action × Reward) n next)) =
        fun next : Action × Reward =>
          History.extendPairHistorySucc history next := by
    funext next j
    by_cases hj : j.1 <= n
    · simp [IicProdIoc, History.extendPairHistorySucc, hj]
    · have hj_le : j.1 <= n + 1 := Finset.mem_Iic.mp j.2
      have h_succ_le : n + 1 <= j.1 :=
        Nat.succ_le_of_lt (lt_of_not_ge hj)
      have hj_eq : j.1 = n + 1 := le_antisymm hj_le h_succ_le
      simp [IicProdIoc, History.extendPairHistorySucc, hj_eq,
        MeasurableEquiv.piSingleton]
  have h_glue_meas :
      Measurable
        (IicProdIoc (X := fun _ : Nat => Action × Reward) n (n + 1)) :=
    measurable_IicProdIoc
  have h_singleton_meas :
      Measurable
        (MeasurableEquiv.piSingleton
          (X := fun _ : Nat => Action × Reward) n) :=
    (MeasurableEquiv.piSingleton
      (X := fun _ : Nat => Action × Reward) n).measurable
  rw [actionRewardPartialTrajectoryKernel]
  rw [ProbabilityTheory.Kernel.partialTraj_succ_self]
  rw [ProbabilityTheory.Kernel.map_apply _ h_glue_meas]
  rw [ProbabilityTheory.Kernel.prod_apply]
  rw [ProbabilityTheory.Kernel.id_apply]
  rw [ProbabilityTheory.Kernel.map_apply _ h_singleton_meas]
  rw [Measure.dirac_prod]
  rw [Measure.map_map h_glue_meas (by fun_prop)]
  rw [Measure.map_map (h_glue_meas.comp (by fun_prop))
    (MeasurableEquiv.piSingleton
      (X := fun _ : Nat => Action × Reward) n).measurable]
  exact
    congrArg
      (fun f =>
        Measure.map f
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate n history))
      h_extend_comp

/--
Canonical regular conditional distribution for the action/reward trajectory
generated by the local history-step kernel family.

This is the Mathlib-backed trajectory-measure side of the open
`COND-EXPECT-REWARD` law-identification route.  It does not identify an
arbitrary ambient `condExpKernel`; it records that, on Mathlib's canonical
`trajMeasure`, conditioning the next action/reward pair on the finite prefix
recovers the configured `actionRewardHistoryStepKernelFamily`.
-/
theorem actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [StandardBorelSpace (Prod Action Reward)]
    [Nonempty (Prod Action Reward)]
    (mu0 : Measure (Prod Action Reward))
    [MeasureTheory.IsProbabilityMeasure mu0]
    (rewardKernel : MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun trajectory : (t : Nat) -> Prod Action Reward =>
          trajectory (n + 1))
        (Preorder.frestrictLe n)
        (ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Prod Action Reward)
          mu0
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate))
      =ᵐ[
        (ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Prod Action Reward)
          mu0
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate)).map
          (Preorder.frestrictLe n)]
        actionRewardHistoryStepKernelFamily rewardKernel policy context state
          hcontext hstate n := by
  exact
    ProbabilityTheory.Kernel.condDistrib_trajMeasure
      (X := fun _ : Nat => Prod Action Reward)
      (a := n)

/--
Canonical reward-marginal regular conditional distribution for the
action/reward trajectory generated by the local history-step kernel family.

This is the `Prod.snd` projection of
`actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure`: on Mathlib's
canonical `trajMeasure`, conditioning the next reward coordinate on the finite
action/reward prefix recovers the reward marginal of the configured
`actionRewardHistoryStepKernelFamily`.
-/
theorem actionRewardHistoryStepKernelFamily_reward_condDistrib_trajMeasure
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [StandardBorelSpace (Prod Action Reward)]
    [StandardBorelSpace Reward]
    [Nonempty (Prod Action Reward)] [Nonempty Reward]
    (mu0 : Measure (Prod Action Reward))
    [MeasureTheory.IsProbabilityMeasure mu0]
    (rewardKernel : MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    Filter.EventuallyEq
      (MeasureTheory.ae
        ((ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Prod Action Reward)
          mu0
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate)).map
          (Preorder.frestrictLe n)))
      (ProbabilityTheory.condDistrib
        (fun trajectory : (t : Nat) -> Prod Action Reward =>
          (trajectory (n + 1)).2)
        (Preorder.frestrictLe n)
        (ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Prod Action Reward)
          mu0
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate)))
      ((actionRewardHistoryStepKernelFamily rewardKernel policy context state
        hcontext hstate n).map Prod.snd) := by
  let stepKernel :=
    actionRewardHistoryStepKernelFamily rewardKernel policy context state
      hcontext hstate
  let trajMeasure :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod Action Reward) mu0 stepKernel
  have hcomp :
      Filter.EventuallyEq
        (MeasureTheory.ae (trajMeasure.map (Preorder.frestrictLe n)))
        (ProbabilityTheory.condDistrib
          (fun trajectory : (t : Nat) -> Prod Action Reward =>
            (trajectory (n + 1)).2)
          (Preorder.frestrictLe n)
          trajMeasure)
        ((ProbabilityTheory.condDistrib
          (fun trajectory : (t : Nat) -> Prod Action Reward =>
            trajectory (n + 1))
          (Preorder.frestrictLe n)
          trajMeasure).map Prod.snd) := by
    have h :=
      ProbabilityTheory.condDistrib_comp
        (Y := fun trajectory : (t : Nat) -> Prod Action Reward =>
          trajectory (n + 1))
        (μ := trajMeasure)
        (mβ := MeasurableSpace.pi)
        ((Preorder.frestrictLe n) :
          ((t : Nat) -> Prod Action Reward) ->
            ((i : Finset.Iic n) -> Prod Action Reward))
        (measurable_pi_apply (n + 1)).aemeasurable
        (f := Prod.snd)
        measurable_snd
    simpa [Function.comp_def] using h
  have hpair :
      Filter.EventuallyEq
        (MeasureTheory.ae (trajMeasure.map (Preorder.frestrictLe n)))
        (ProbabilityTheory.condDistrib
          (fun trajectory : (t : Nat) -> Prod Action Reward =>
            trajectory (n + 1))
          (Preorder.frestrictLe n)
          trajMeasure)
        (stepKernel n) := by
    simpa [stepKernel, trajMeasure] using
      actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure
        mu0 rewardKernel policy context state hcontext hstate n
  filter_upwards [hcomp, hpair] with history hcomp_eq hpair_eq
  rw [hcomp_eq]
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_snd]
  rw [hpair_eq]
  rw [← ProbabilityTheory.Kernel.map_apply _ measurable_snd]

/--
Canonical selected-reward regular conditional distribution for the
action/reward trajectory generated by the local history-step kernel family.

This rewrites the reward marginal from
`actionRewardHistoryStepKernelFamily_reward_condDistrib_trajMeasure` into the
selected context/action reward measure at the frozen finite pair history.
-/
theorem actionRewardHistoryStepKernelFamily_selectedMeasure_condDistrib_trajMeasure
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [StandardBorelSpace (Prod Action Reward)]
    [StandardBorelSpace Reward]
    [Nonempty (Prod Action Reward)] [Nonempty Reward]
    (mu0 : Measure (Prod Action Reward))
    [MeasureTheory.IsProbabilityMeasure mu0]
    (rewardKernel : MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    Filter.EventuallyEq
      (MeasureTheory.ae
        ((ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Prod Action Reward)
          mu0
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate)).map
          (Preorder.frestrictLe n)))
      (ProbabilityTheory.condDistrib
        (fun trajectory : (t : Nat) -> Prod Action Reward =>
          (trajectory (n + 1)).2)
        (Preorder.frestrictLe n)
        (ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Prod Action Reward)
          mu0
          (actionRewardHistoryStepKernelFamily rewardKernel policy context state
            hcontext hstate)))
      (fun history : (i : Finset.Iic n) -> Prod Action Reward =>
        selectedMeasure rewardKernel
          (context n history) ((policy n).action (state n history))) := by
  have hreward :=
    actionRewardHistoryStepKernelFamily_reward_condDistrib_trajMeasure
      mu0 rewardKernel policy context state hcontext hstate n
  filter_upwards [hreward] with history hreward_eq
  rw [hreward_eq]
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_snd]
  exact
    actionRewardHistoryStepKernelFamily_reward_map
      rewardKernel policy context state hcontext hstate n history

end RewardKernel
end BanditRLProof
