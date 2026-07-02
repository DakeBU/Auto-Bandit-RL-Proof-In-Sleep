I’ll keep this in the ETC deterministic count layer and avoid the full trace or commit phase. The next safest leaf is a small reusable cycle/shift helper before proving the full m * K count.

Thought for 5m 23s
1. Next single executable leaf

Do one ETC shifted-cycle count lemma before the full m * K theorem.

Recommended row:

ETC-ROUND-ROBIN-ADD-K-COUNT

Recommended theorem:

lean
theorem ETC.pullCount_exploreArm_add_K_eq_add_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (t : Nat) :
    pullCount (ETC.exploreArm spec) a (t + K) =
      pullCount (ETC.exploreArm spec) a t + 1

This is the right intermediate leaf. It says every length-K extension of the round-robin exploration trace adds exactly one pull of every arm. It is stronger and more reusable than the first-cycle theorem, but still much smaller than the full m * K count theorem.

2. Why not prove pullCount ... (m * K) = m immediately?

The full theorem should be the next count theorem after this recurrence:

lean
pullCount (ETC.exploreArm spec) a (t + K)
  =
pullCount (ETC.exploreArm spec) a t + 1

Then the multiple-cycle theorem is just induction on m, using t := m * K.

This avoids doing all periodicity and pullCount_succ arithmetic inside the larger multiplication proof.

3. File placement

Put it in:

BanditRLProof/Algorithms/ETCCountLemmas.lean

beside:

lean
ETC.pullCount_exploreArm_K_eq_one

Do not put it in Algorithms/ETC.lean; that file should remain the selector/primitive API. This theorem is already a pullCount fact.

4. Imports

The existing count-lemma file likely already has enough:

lean
import Mathlib.Data.Finset.Card
import BanditRLProof.MathlibWrappers
import BanditRLProof.Algorithms.ETC

For this new proof, the essential local APIs are:

lean
pullCount_succ
ETC.pullCount_exploreArm_K_eq_one
ETC.exploreArm_add_K

If pullCount_succ is not exposed through MathlibWrappers, add:

lean
import BanditRLProof.LeafLemmas

A clean import set is therefore:

lean
import Mathlib.Data.Finset.Card
import BanditRLProof.MathlibWrappers
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETC

Do not import regret bounds, probability, expectation, ENNReal, concentration, or the project root.

5. Exact Lean-facing statement and proof route
lean
namespace BanditRLProof

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
      · simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end BanditRLProof

The proof route is:

Induct on the starting time t.

Base case is the already compiled first-cycle theorem:

lean
ETC.pullCount_exploreArm_K_eq_one

Successor case unfolds both sides with:

lean
pullCount_succ

Use periodicity:

lean
ETC.exploreArm_add_K spec t

Close the Nat arithmetic by cases on:

lean
ETC.exploreArm spec t = a
6. Local APIs to reuse

Reuse exactly:

lean
ETC.pullCount_exploreArm_K_eq_one
ETC.exploreArm_add_K
pullCount_succ

Do not use:

lean
pullCount_eq_finset_filter_card
ETC.exploreArm_eq_iff_mod_eq_val
pseudoRegret
RegretCountBounds
Expectation*

The prior Finset count theorem is only needed for the base case, already encapsulated by ETC.pullCount_exploreArm_K_eq_one.

7. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(a : Fin K)
(t : Nat)

Do not add:

lean
0 < K
DecidableEq (Fin K)
Fintype (Fin K)
Measure
MeasurableSpace
Rat
ENNReal
pseudoRegret
concentration assumptions

The positivity proof is already inside:

lean
spec.hK : 0 < K

and decidable equality for Fin K should synthesize automatically.

8. Classification

Classify this as:

ETC-ROUND-ROBIN-ADD-K-COUNT:
  project-local compiled ETC deterministic count scaffold

It is not:

imported
Mathlib candidate
theorem-card-only
probability/concentration leaf
ETC final regret theorem

It is a project-local executable lemma supporting:

round_robin_exploration_counts
multiple-cycle exploration counts
pull_count_bound_after_commit
ETC deterministic regret skeleton
9. Failure policy

Use a fail-closed policy.

If this leaf fails:

First confirm pullCount_succ is imported:

lean
import BanditRLProof.LeafLemmas

If rw [Nat.succ_add] does not hit the goal, replace it with:

lean
change pullCount (ETC.exploreArm spec) a (Nat.succ (t + K)) =
  pullCount (ETC.exploreArm spec) a (Nat.succ t) + 1

If rw [pullCount_succ] rewrites too much or too little, use a calc proof:

lean
calc
  pullCount (ETC.exploreArm spec) a (Nat.succ (t + K))
      =
    pullCount (ETC.exploreArm spec) a (t + K)
      + if ETC.exploreArm spec (t + K) = a then 1 else 0 := by
        rw [pullCount_succ]
  _ =
    pullCount (ETC.exploreArm spec) a t + 1
      + if ETC.exploreArm spec t = a then 1 else 0 := by
        rw [ih, hper]
  _ =
    pullCount (ETC.exploreArm spec) a (Nat.succ t) + 1 := by
        rw [pullCount_succ]
        by_cases h : ETC.exploreArm spec t = a
        · simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

Do not switch to a full m * K theorem in the same batch.

Do not define the full ETC action trace.

Do not import probability, expectation, concentration, empirical means, commit argmax, or all of Mathlib.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

10. Minimal batch

Complete only:

ETC-ROUND-ROBIN-ADD-K-COUNT

with:

one theorem in BanditRLProof/Algorithms/ETCCountLemmas.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next leaf should be the full multiple-cycle theorem:

lean
pullCount (ETC.exploreArm spec) a (m * K) = m

using this new add-K count recurrence.