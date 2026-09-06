import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MathlibWrappers

/-!
# Measurability of local pseudo-regret

This module keeps regret measurability before expectation.  It only proves that
the local deterministic pseudo-regret quantity becomes a measurable random
variable when the action trace is timewise measurable.
-/

universe u

namespace BanditRLProof

/--
The local pseudo-regret process is measurable as a random variable at each
finite horizon.

This is the narrow `MEAS-REGRET` bridge.  It does not introduce probability
measures, expectations, filtrations, or concentration assumptions.
-/
theorem measurable_pseudoRegret
    {Omega : Type u}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    Measurable
      (fun omega : Omega => pseudoRegret model (action omega) n) := by
  have hgap : Measurable (fun a : Fin K => model.gap a) := by
    exact measurable_of_finite (fun a : Fin K => model.gap a)
  have hsum :
      Measurable
        (fun omega : Omega =>
          (Finset.range n).sum
            (fun t : Nat => model.gap (action omega t))) := by
    refine Finset.induction_on (Finset.range n) ?h_empty ?h_insert
    · simp
    · intro t s ht ih
      have hterm :
          Measurable
            (fun omega : Omega => model.gap (action omega t)) := by
        exact hgap.comp (haction t)
      simpa [Finset.sum_insert, ht] using hterm.add ih
  have hfun :
      (fun omega : Omega => pseudoRegret model (action omega) n)
        =
      (fun omega : Omega =>
        (Finset.range n).sum
          (fun t : Nat => model.gap (action omega t))) := by
    funext omega
    simpa using
      (pseudoRegret_eq_finset_sum
        (model := model)
        (action := action omega)
        (t := n))
  rw [hfun]
  exact hsum

end BanditRLProof
