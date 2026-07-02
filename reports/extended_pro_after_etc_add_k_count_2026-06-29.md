I’ll keep this to one ETC count leaf. The key choice is using m * K and inducting on m, matching the existing add-K recurrence.

Thought for 3m 26s
1. Next single executable leaf

Yes. The next leaf should be the multiple-full-cycle ETC count theorem.

Recommended row:

ETC-ROUND-ROBIN-MUL-K-COUNT

Recommended theorem:

lean
theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m

This is now small because the compiled recurrence already says:

lean
pullCount (ETC.exploreArm spec) a (t + K)
  =
pullCount (ETC.exploreArm spec) a t + 1

No generic segment decomposition is needed before this. The add-K recurrence is the segment lemma.

2. Horizon orientation

Use:

lean
m * K

not K * m.

Reason: with induction on m, Lean’s Nat.succ_mul rewrites the successor horizon into exactly the form needed by the compiled add-K recurrence:

lean
Nat.succ m * K = m * K + K

Then the step is direct:

lean
pullCount ... (m * K + K)
  =
pullCount ... (m * K) + 1
  =
m + 1

The K * m orientation would require Nat.mul_succ, which is also viable, but m * K reads as “m full cycles of length K” and matches the add-K recurrence cleanly.

3. File placement

Put it in:

BanditRLProof/Algorithms/ETCCountLemmas.lean

beside:

lean
ETC.pullCount_exploreArm_K_eq_one
ETC.pullCount_exploreArm_add_K_eq_add_one

Do not put it in Algorithms/ETC.lean; this is a pullCount theorem, not a primitive selector theorem.

4. Imports

The existing count-lemma file should already have enough. Minimal expected imports:

lean
import Mathlib.Data.Finset.Card
import BanditRLProof.MathlibWrappers
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETC

The new theorem itself only needs:

lean
ETC.pullCount_exploreArm_add_K_eq_add_one
pullCount

No new Mathlib import should be required beyond what the file already uses.

Do not import probability, expectation, regret bounds, ENNReal, concentration, empirical means, or the project root.

5. Exact Lean-facing statement and proof
lean
namespace BanditRLProof

theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m := by
  induction m with
  | zero =>
      simp [pullCount]
  | succ m ih =>
      simpa [Nat.succ_mul, ih] using
        ETC.pullCount_exploreArm_add_K_eq_add_one
          spec a (m * K)

end BanditRLProof

If the final simpa is too terse locally, use this more explicit version:

lean
theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m := by
  induction m with
  | zero =>
      simp [pullCount]
  | succ m ih =>
      rw [Nat.succ_mul]
      rw [ETC.pullCount_exploreArm_add_K_eq_add_one spec a (m * K)]
      rw [ih]
      rfl

If rfl does not close the final m + 1 = Nat.succ m, replace it with:

lean
      simp [Nat.succ_eq_add_one]
6. Local APIs to reuse

Reuse exactly:

lean
ETC.pullCount_exploreArm_add_K_eq_add_one

and, in the base case, the definition/simp behavior of:

lean
pullCount

Do not use:

lean
pullCount_eq_finset_filter_card
ETC.pullCount_exploreArm_K_eq_one
ETC.exploreArm_eq_iff_mod_eq_val
pseudoRegret
REGRET-COUNT-BOUND
Expectation*

The first-cycle theorem is already encapsulated by the add-K recurrence and is not needed directly.

7. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(a : Fin K)
(m : Nat)

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

spec.hK : 0 < K is already inside ETC.Spec K, and no explicit decidability/finiteness contract is needed for this proof.

8. Classification

Classify this as:

ETC-ROUND-ROBIN-MUL-K-COUNT:
  project-local compiled ETC deterministic count scaffold

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
ETC final regret theorem

It is a project-local executable lemma supporting:

round_robin_exploration_counts
pull_count_bound_after_commit
ETC deterministic regret skeleton
9. Failure policy

Use a fail-closed policy.

If this leaf fails:

First try the explicit rw proof instead of the compact simpa.

If Nat.succ_mul does not rewrite as expected, use:

lean
change pullCount (ETC.exploreArm spec) a (m * K + K) = Nat.succ m

after the successor case goal is shown.

If the add-K theorem does not match, instantiate it explicitly:

lean
have hstep :=
  ETC.pullCount_exploreArm_add_K_eq_add_one
    (spec := spec) (a := a) (t := m * K)
rw [hstep]

If final Nat arithmetic is brittle, close with:

lean
simp [Nat.succ_eq_add_one]

Do not switch to defining the full ETC action trace.

Do not start empirical means, commit argmax, concentration, probability, or final ETC regret work in this batch.

Do not add broad imports or theorem-card placeholders.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

10. Minimal batch

Complete only:

ETC-ROUND-ROBIN-MUL-K-COUNT

with:

one theorem in BanditRLProof/Algorithms/ETCCountLemmas.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide between an explorationPulls specialization:

lean
pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K)
  =
spec.explorationPulls

and the first exploration-phase action-trace boundary.