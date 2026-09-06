import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Cast.Basic
import BanditRLProof.MathlibWrappers

/-!
# Deterministic regret decompositions

This module consumes the Mathlib-backed finite bookkeeping wrappers.  It should
stay deterministic: probability, measurability, and concentration imports belong
in later layers.
-/

namespace BanditRLProof

section PullCountRegret

variable (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat)

/--
Pseudo-regret decomposes into an arm-indexed sum of each arm gap multiplied by
its pull count.

This is the deterministic `REGRET-PULLCOUNT` bridge.  It consumes the compiled
`Finset.range` wrappers instead of reopening the recursive definitions of
`pseudoRegret` or `pullCount`.
-/
theorem pseudoRegret_eq_finset_sum_gap_mul_pullCount :
    pseudoRegret model action t =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (pullCount action a t : Rat)) := by
  rw [pseudoRegret_eq_finset_sum]
  rw [(Finset.sum_fiberwise' (s := Finset.range t) (g := action)
    (f := fun a : Fin K => model.gap a)).symm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_const
    (s := (Finset.range t).filter (fun s : Nat => action s = a))
    (b := model.gap a)]
  have hcount :=
    pullCount_eq_finset_filter_card (action := action) (a := a) (t := t)
  rw [hcount.symm]
  exact nsmul_eq_mul' (model.gap a) (pullCount action a t)

end PullCountRegret

end BanditRLProof
