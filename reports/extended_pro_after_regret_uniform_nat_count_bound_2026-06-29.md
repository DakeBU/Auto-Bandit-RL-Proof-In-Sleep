I’ll keep the next step inside the deterministic ETC exploreArm layer, avoiding a full policy trace while first proving the small round-robin selector/count fact needed downstream.

Thought for 4m 15s
1. Next single executable leaf

Do the first ETC-specific round-robin count scaffold:

ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT

Recommended theorem:

lean
theorem ETC.pullCount_exploreArm_K_eq_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a K = 1

This is the right next leaf because it is the smallest actual count theorem for ETC. It uses the existing ETC.exploreArm directly as an ActionTrace (Fin K), without defining the full ETC action trace with commit behavior. The full trace should wait until the round-robin exploration facts are stable.

2. Should this define an ETC action trace first?

No.

ETC.exploreArm spec already has type:

lean
Nat -> Fin K

so it can be consumed by:

lean
pullCount

directly. Defining a full ETC trace now would force extra design choices about exploration-vs-commit phases and empirical argmax behavior. This leaf should prove one local fact about the existing round-robin primitive.

3. File placement

Use a new small file:

BanditRLProof/Algorithms/ETCCountLemmas.lean

Import it from:

lean
BanditRLProof.lean

Keep it separate from Algorithms/ETC.lean if that file currently only defines ETC primitives. The count file can grow into the deterministic ETC count scaffold layer.

4. Imports

Use:

lean
import Mathlib.Data.Finset.Card
import BanditRLProof.MathlibWrappers
import BanditRLProof.Algorithms.ETC

Reason:

BanditRLProof.Algorithms.ETC gives:

lean
ETC.Spec
ETC.exploreArm
ETC.exploreArm_val
ETC.exploreArm_eq_of_mod_eq
ETC.exploreArm_add_K

BanditRLProof.MathlibWrappers gives:

lean
pullCount_eq_finset_filter_card

Mathlib.Data.Finset.Card is the explicit boundary for filtered finset cardinalities and singleton card simplification.

Do not import regret bounds, probability, expectation, ENNReal, concentration, or the project root.

5. Exact Lean-facing statement and proof route
lean
import Mathlib.Data.Finset.Card
import BanditRLProof.MathlibWrappers
import BanditRLProof.Algorithms.ETC

namespace BanditRLProof

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
      have hval := congrArg Fin.val hsa
      have hmod : s % K = a.val := by
        simpa [ETC.exploreArm] using hval
      have hsmod : s % K = s := Nat.mod_eq_of_lt hslt
      rw [hsmod] at hmod
      exact hmod
    · intro hs
      subst s
      constructor
      · exact a.isLt
      · apply Fin.ext
        simp [ETC.exploreArm, Nat.mod_eq_of_lt a.isLt]

  rw [hfilter]
  simp

end BanditRLProof
6. Local APIs to reuse

Reuse exactly:

lean
pullCount_eq_finset_filter_card
ETC.exploreArm
ETC.exploreArm_val

The proof should establish that, within the first cycle Finset.range K, the filtered set of times selecting arm a is exactly:

lean
({a.val} : Finset Nat)

Do not use:

lean
pseudoRegret
REGRET-COUNT-BOUND
REGRET-NAT-COUNT-BOUND
REGRET-UNIFORM-NAT-COUNT-BOUND
Expectation*

This is an ETC count lemma only.

7. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(a : Fin K)

Do not add:

lean
0 < K
DecidableEq (Fin K)
Measure
MeasurableSpace
IsProbabilityMeasure
ENNReal
Rat
Regret
Concentration assumptions

The positivity contract is already inside:

lean
spec.hK : 0 < K

and DecidableEq (Fin K) should synthesize automatically.

8. Classification

Classify this as:

ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT:
  project-local compiled ETC deterministic count scaffold

It is not:

imported
Mathlib candidate
theorem-card-only
probability/concentration leaf
ETC regret theorem

It is a project-local executable leaf.

It is a prerequisite for:

round_robin_exploration_counts
pull_count_bound_after_commit
regret_from_pull_count_bounds
ETC deterministic regret skeleton
9. Failure policy

Use a fail-closed policy.

If this leaf fails:

First check that the file imports:

lean
import BanditRLProof.MathlibWrappers
import BanditRLProof.Algorithms.ETC

If the filtered-finset ext proof is brittle, isolate this private helper:

lean
private theorem ETC.exploreArm_eq_iff_eq_val_of_lt
    {K : Nat}
    (spec : ETC.Spec K) {s : Nat} (hs : s < K) (a : Fin K) :
    ETC.exploreArm spec s = a ↔ s = a.val := by
  constructor
  · intro hsa
    have hval := congrArg Fin.val hsa
    have hmod : s % K = a.val := by
      simpa [ETC.exploreArm] using hval
    have hsmod : s % K = s := Nat.mod_eq_of_lt hs
    rw [hsmod] at hmod
    exact hmod
  · intro hs_eq
    subst s
    apply Fin.ext
    simp [ETC.exploreArm, Nat.mod_eq_of_lt a.isLt]

Then use that helper inside the Finset.ext proof.

If Nat.mod_eq_of_lt does not simplify, make the proof explicit:

lean
have hsmod : s % K = s := Nat.mod_eq_of_lt hslt

If singleton-card simplification fails after rw [hfilter], use:

lean
simp

or:

lean
exact Finset.card_singleton a.val

depending on the goal orientation.

Do not define the full ETC action trace in this batch.

Do not start ETC regret, probability, concentration, or empirical-mean argmax work.

Do not add sorry, axioms, theorem-card placeholders, or broad imports.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

10. Batch size

Complete only:

ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT

with:

BanditRLProof/Algorithms/ETCCountLemmas.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to generalize this to m * K exploration pulls or define the first ETC exploration-phase action trace.