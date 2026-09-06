import Mathlib.Data.Nat.Cast.Order.Basic
import BanditRLProof.Algorithms.ETCRegretLemmas

/-!
# ETC wrong-commit regret assembly

This module gives a pointwise bridge from the deterministic fixed-commit ETC
regret scaffolds to a wrong-commit-shaped suffix penalty.  It deliberately
stays below integration, probability bounds, concentration, filtrations, and a
final ETC expected-regret theorem.
-/

universe u

namespace BanditRLProof
namespace ETC

/--
For an `Omega`-indexed commit selector, fixed-commit ETC regret after a suffix
is bounded by the exploration budget plus a suffix penalty that vanishes when
the selected commit arm is the model's `bestArm`.

The explicit `badGapBound` is the local bridge to a later probability layer:
the suffix cost is charged only on the wrong-commit branch.
-/
theorem pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commit : Omega -> Fin K) (r : Nat) (badGapBound : Rat)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (omega : Omega) :
    pseudoRegret model (ETC.actionWithCommit spec (commit omega))
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) *
        (if commit omega = model.bestArm then 0 else badGapBound)) := by
  by_cases hcommit : commit omega = model.bestArm
  · have hbest :
      pseudoRegret model (ETC.actionWithCommit spec (commit omega))
          (spec.explorationPulls * K + r) <=
        ((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) *
          (((spec.explorationPulls : Nat) : Rat)) :=
      ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm
        (spec := spec)
        (model := model)
        (commitArm := commit omega)
        (r := r)
        (hcommit := hcommit)
    simpa [hcommit] using hbest
  · have hphase :
      pseudoRegret model (ETC.actionWithCommit spec (commit omega))
          (spec.explorationPulls * K + r) <=
        ((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) *
          (((spec.explorationPulls : Nat) : Rat)) +
        (((r : Nat) : Rat) * model.gap (commit omega)) :=
      ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
        (spec := spec)
        (model := model)
        (commitArm := commit omega)
        (r := r)
    have hr_nonneg : (0 : Rat) <= (((r : Nat) : Rat)) := by
      exact_mod_cast Nat.zero_le r
    have hsuffix :
        (((r : Nat) : Rat) * model.gap (commit omega)) <=
          (((r : Nat) : Rat) * badGapBound) :=
      mul_le_mul_of_nonneg_left
        (hbadGap (commit omega) hcommit)
        hr_nonneg
    have hrhs :
        ((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) *
          (((spec.explorationPulls : Nat) : Rat)) +
        (((r : Nat) : Rat) * model.gap (commit omega)) <=
        ((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) *
          (((spec.explorationPulls : Nat) : Rat)) +
        (((r : Nat) : Rat) * badGapBound) :=
      add_le_add
        (le_refl
          (((Finset.univ : Finset (Fin K)).sum
            (fun a : Fin K => model.gap a)) *
            (((spec.explorationPulls : Nat) : Rat))))
        hsuffix
    exact le_trans hphase (by simpa [hcommit] using hrhs)

end ETC
end BanditRLProof
