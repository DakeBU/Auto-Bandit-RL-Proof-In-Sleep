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
