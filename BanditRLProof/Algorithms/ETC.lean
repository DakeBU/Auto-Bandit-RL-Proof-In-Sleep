import BanditRLProof.Regret

/-!
# Explore-Then-Commit surfaces
-/

namespace BanditRLProof
namespace ETC

/-- Parameters for a finite-arm Explore-Then-Commit run. -/
structure Spec (K : Nat) where
  hK : 0 < K
  explorationPulls : Nat

/-- Round-robin exploration arm at time `t`. -/
def exploreArm (spec : Spec K) (t : Nat) : Fin K :=
  ⟨t % K, Nat.mod_lt t spec.hK⟩

@[simp] theorem exploreArm_val (spec : Spec K) (t : Nat) :
    (exploreArm spec t).val = t % K := rfl

theorem exploreArm_eq_of_mod_eq (spec : Spec K) {s t : Nat}
    (h : s % K = t % K) :
    exploreArm spec s = exploreArm spec t := by
  apply Fin.ext
  exact h

theorem exploreArm_eq_iff_mod_eq_val (spec : Spec K) (t : Nat) (a : Fin K) :
    exploreArm spec t = a ↔ t % K = a.val := by
  constructor
  · intro h
    simpa [exploreArm_val] using congrArg Fin.val h
  · intro h
    apply Fin.ext
    simpa [exploreArm_val] using h

theorem exploreArm_add_K (spec : Spec K) (t : Nat) :
    exploreArm spec (t + K) = exploreArm spec t := by
  apply exploreArm_eq_of_mod_eq
  simp

/-- Commit-phase selector.  A concrete theorem should replace this by argmax. -/
structure CommitOracle (K : Nat) where
  choose : (Fin K → Rat) → Fin K
  card : String

/-- The proof-DAG leaves usually needed for ETC regret formalization. -/
def obligationNames : List String :=
  [ "round_robin_exploration_counts"
  , "empirical_mean_argmax_commit"
  , "subgaussian_wrong_commit_probability"
  , "pull_count_bound_after_commit"
  , "regret_from_pull_count_bounds"
  ]

end ETC
end BanditRLProof
