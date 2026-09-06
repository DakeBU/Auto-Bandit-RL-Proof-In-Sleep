import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import BanditRLProof.MeasurableSums
import BanditRLProof.MathlibWrappers

/-!
# Measurability of local bandit quantities

This module connects generic measurable finite-sum bridges back to the local
recursive quantities used by the bandit vocabulary.
-/

universe u v

namespace BanditRLProof

private theorem sumRewards_eq_finset_range_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type v}
    [DecidableEq Action] [AddCommMonoid Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (a : Action) (n : Nat) (omega : Omega) :
    sumRewards (action omega) (reward omega) a n =
      (Finset.range n).sum
        (fun t : Nat =>
          (({omega' : Omega | action omega' t = a} : Set Omega).indicator
            (fun omega' : Omega => reward omega' t)) omega) := by
  calc
    sumRewards (action omega) (reward omega) a n
        =
      ((Finset.range n).filter
        (fun t : Nat => action omega t = a)).sum
        (fun t : Nat => reward omega t) := by
          simpa using
            (sumRewards_eq_finset_filter_sum
              (action := action omega)
              (reward := reward omega)
              (a := a)
              (t := n))
    _ =
      (Finset.range n).sum
        (fun t : Nat =>
          (({omega' : Omega | action omega' t = a} : Set Omega).indicator
            (fun omega' : Omega => reward omega' t)) omega) := by
          simpa using
            (Finset.sum_indicator_eq_sum_filter
              (s := Finset.range n)
              (f := fun t (omega' : Omega) => reward omega' t)
              (t := fun t : Nat =>
                {omega' : Omega | action omega' t = a})
              (g := fun _ : Nat => omega)).symm

/--
The local recursive selected-reward accumulator is measurable when action and
reward traces are timewise measurable.

This is the `MEAS-SUMREWARDS` bridge.  It is still only a measurability result:
no expectation, probability measure, filtration, or concentration structure is
introduced here.
-/
theorem measurable_sumRewards
    {Omega : Type u} {Action : Type v} {Reward : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => sumRewards (action omega) (reward omega) a n) := by
  have hsum :
      Measurable
        (fun omega : Omega =>
          (Finset.range n).sum
            (fun t : Nat =>
              (({omega' : Omega | action omega' t = a} : Set Omega).indicator
                (fun omega' : Omega => reward omega' t)) omega)) := by
    exact measurable_finset_sum_indicator_reward
      action reward haction hreward a (Finset.range n)
  have hfun :
      (fun omega : Omega => sumRewards (action omega) (reward omega) a n)
        =
      (fun omega : Omega =>
        (Finset.range n).sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega)) := by
    funext omega
    exact sumRewards_eq_finset_range_indicator_reward action reward a n omega
  rw [hfun]
  exact hsum

end BanditRLProof
