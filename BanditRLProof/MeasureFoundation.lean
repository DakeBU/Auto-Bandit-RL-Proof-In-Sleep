import Mathlib.MeasureTheory.MeasurableSpace.Basic
import BanditRLProof.Core

/-!
# Minimal measurable action-event foundations

This module starts the probability-facing layer with measurable events only.
It deliberately avoids measure, integration, probability, filtration, and
concentration imports.
-/

universe u v w

namespace BanditRLProof

section ActionEvents

/--
If every time-indexed action random variable is measurable, then the event that
the action at a fixed time equals a fixed arm is measurable.

This is the `MEAS-FIN-ACTION` canary.  The statement is more general than finite
actions: it only needs singleton measurability of the action space.
-/
theorem measurableSet_actionTrace_eval_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasurableSet {omega : Omega | action omega t = a} := by
  simpa [Set.preimage] using
    ((hmeas t) (MeasurableSet.singleton a))

/--
The indicator of a measurable action-equality event with a constant value is
measurable.

This is the `MEAS-PULL-INDICATOR` bridge.  It remains scalar-agnostic so later
expectation work can choose the codomain deliberately.
-/
theorem measurable_actionTrace_eval_eq_indicator_const
    {Omega : Type u} {Action : Type v} {Beta : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [Zero Beta]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) (c : Beta) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun _ : Omega => c)) := by
  exact Measurable.indicator measurable_const
    (measurableSet_actionTrace_eval_eq action hmeas a t)

/--
The selected-reward contribution for a fixed action event is measurable when
the action and reward traces are timewise measurable.

This is the `MEAS-REWARD` bridge.  It deliberately stays at the
measurability layer and does not choose an expectation or scalar algebra route.
-/
theorem measurable_actionTrace_eval_eq_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [Zero Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (t : Nat) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun omega : Omega => reward omega t)) := by
  exact Measurable.indicator (hreward t)
    (measurableSet_actionTrace_eval_eq action haction a t)

end ActionEvents

end BanditRLProof
