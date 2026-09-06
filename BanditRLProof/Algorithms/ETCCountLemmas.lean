import Mathlib.Data.Finset.Card
import BanditRLProof.MathlibWrappers
import BanditRLProof.Algorithms.ETC

/-!
# Deterministic ETC count lemmas

This module records small Explore-Then-Commit count facts over the existing
round-robin exploration primitive.  It deliberately stays below full ETC traces,
commit behavior, probability, concentration, and regret bounds.
-/

namespace BanditRLProof

/--
During the first full round-robin exploration cycle, every arm is pulled
exactly once.

This is the `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` project-local deterministic
count scaffold.
-/
theorem ETC.pullCount_exploreArm_K_eq_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a K = 1 := by
  rw [pullCount_eq_finset_filter_card]
  have hfilter :
      ((Finset.range K).filter
        (fun s : Nat => ETC.exploreArm spec s = a))
        =
      ({a.val} : Finset Nat) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · intro hs
      rcases hs with ⟨hslt, hsa⟩
      have hval : s % K = a.val := by
        simpa [ETC.exploreArm_val] using congrArg Fin.val hsa
      have hsmod : s % K = s := Nat.mod_eq_of_lt hslt
      rw [hsmod] at hval
      exact hval
    · intro hs
      subst s
      constructor
      · exact a.isLt
      · apply Fin.ext
        simp [ETC.exploreArm_val, Nat.mod_eq_of_lt a.isLt]
  rw [hfilter]
  simp

/--
Extending a round-robin ETC exploration prefix by one full cycle adds exactly
one pull of every arm.

This is the `ETC-ROUND-ROBIN-ADD-K-COUNT` project-local deterministic count
scaffold.
-/
theorem ETC.pullCount_exploreArm_add_K_eq_add_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (t : Nat) :
    pullCount (ETC.exploreArm spec) a (t + K) =
      pullCount (ETC.exploreArm spec) a t + 1 := by
  induction t with
  | zero =>
      simpa using ETC.pullCount_exploreArm_K_eq_one spec a
  | succ t ih =>
      have hper :
          ETC.exploreArm spec (t + K) = ETC.exploreArm spec t :=
        ETC.exploreArm_add_K spec t
      rw [Nat.succ_add]
      rw [pullCount_succ]
      rw [pullCount_succ]
      rw [ih]
      rw [hper]
      by_cases h : ETC.exploreArm spec t = a
      · simp [h, Nat.add_comm]
      · simp [h, Nat.add_comm]

/--
Across `m` full round-robin ETC exploration cycles, every arm is pulled exactly
`m` times.

This is the `ETC-ROUND-ROBIN-MUL-K-COUNT` project-local deterministic count
scaffold.
-/
theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Nat.succ_mul]
      rw [ETC.pullCount_exploreArm_add_K_eq_add_one spec a (m * K)]
      rw [ih]

/--
At the configured ETC exploration horizon, every arm has been pulled exactly
`spec.explorationPulls` times.

This is the `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` project-local
deterministic count adapter.
-/
theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls := by
  simpa using
    ETC.pullCount_exploreArm_mul_K_eq
      (spec := spec)
      (a := a)
      (m := spec.explorationPulls)

end BanditRLProof
