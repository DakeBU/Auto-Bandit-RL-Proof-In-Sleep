import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation

/-!
# Measurable finite sums of selected reward contributions

This module keeps the probability-facing layer before integration.  It only
proves measurability of finite sums built from the selected-reward indicator
bridge in `MeasureFoundation`.
-/

universe u v w

namespace BanditRLProof

/--
Finite sums of selected-reward indicator contributions are measurable.

This is the `MEAS-SELECTED-REWARD-FINITE-SUM` bridge.  The statement is over an
arbitrary finite set of times so later range, window, or stopped-prefix
corollaries can instantiate the same local API.
-/
theorem measurable_finset_sum_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (s : Finset Nat) :
    Measurable
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega)) := by
  refine Finset.induction_on s ?h_empty ?h_insert
  · simp
  · intro t s ht ih
    have hterm :
        Measurable
          (fun omega : Omega =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega) := by
      exact measurable_actionTrace_eval_eq_indicator_reward
        action reward haction hreward a t
    simpa [Finset.sum_insert, ht] using hterm.add ih

end BanditRLProof
