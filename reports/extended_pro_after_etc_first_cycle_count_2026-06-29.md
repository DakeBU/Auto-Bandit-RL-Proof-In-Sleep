I’ll keep this to one ETC count leaf. The key choice is whether to prove the general m * K result now or first add a stabilizing modular block-count helper.

Thought for 4m 20s
1. Next single executable leaf

Do one smaller modular ETC helper first, not the m * K count theorem yet.

Recommended row:

ETC-EXPLOREARM-EQ-IFF-MOD

Recommended theorem:

lean
theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val

This is the right next leaf because the first-cycle proof already used this reasoning internally. Exposing it as public API will make the later m * K theorem cleaner and less brittle.

2. Why not m * K immediately?

The multiple-cycle theorem is the right next count goal, but it should depend on a small public modular characterization:

lean
ETC.exploreArm spec t = a ↔ t % K = a.val

Without that helper, the m * K proof will likely repeat low-level Fin.ext, congrArg Fin.val, and % K reasoning inside a larger counting argument. That is avoidable technical debt.

Do not define the full ETC action trace yet. The current ETC.exploreArm is enough for round-robin exploration-phase facts.

3. Exact Lean-facing statement

Put this near the ETC primitive API. I recommend adding it to:

BanditRLProof/Algorithms/ETC.lean

beside:

lean
ETC.exploreArm_val
ETC.exploreArm_eq_of_mod_eq
ETC.exploreArm_add_K

Statement:

lean
namespace BanditRLProof

theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    simpa [ETC.exploreArm] using hval
  · intro h
    apply Fin.ext
    simpa [ETC.exploreArm] using h

end BanditRLProof

If you prefer not to modify Algorithms/ETC.lean, put it in:

BanditRLProof/Algorithms/ETCCountLemmas.lean

but semantically it belongs with the core exploreArm API.

4. Imports

If added to Algorithms/ETC.lean, no new import should be needed beyond what that file already has.

If added to ETCCountLemmas.lean, no new import should be needed beyond:

lean
import BanditRLProof.Algorithms.ETC

Do not import:

lean
Mathlib.Data.Finset.Card
BanditRLProof.MathlibWrappers
BanditRLProof.RegretCountBounds
MeasureTheory
ENNReal
Probability
Concentration

This leaf does not mention pullCount, Finset, regret, or probability.

5. Local APIs to use

Use only:

lean
ETC.exploreArm

Optionally the first direction can use:

lean
ETC.exploreArm_val

but direct simplification via [ETC.exploreArm] is likely sufficient.

Do not use:

lean
ETC.pullCount_exploreArm_K_eq_one
pullCount_eq_finset_filter_card
ETC.exploreArm_add_K

This theorem should become a primitive helper that later count lemmas consume.

6. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(t : Nat)
(a : Fin K)

No extra assumption:

lean
(hK : 0 < K)

is needed because spec.hK : 0 < K is already inside ETC.Spec K.

Do not add:

lean
DecidableEq (Fin K)
Fintype (Fin K)
Measure
MeasurableSpace
Rat
ENNReal
pseudoRegret
pullCount
7. Classification

Classify this as:

ETC-EXPLOREARM-EQ-IFF-MOD:
  project-local compiled ETC modular helper

It is not:

imported
Mathlib candidate
theorem-card-only
probability/concentration leaf
ETC regret theorem

It is a small project-local executable lemma supporting:

round_robin_exploration_counts
multiple-cycle exploration counts
pull_count_bound_after_commit
8. Failure policy

Use a fail-closed policy.

If this leaf fails:

First try the proof with ETC.exploreArm_val explicitly:

lean
theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val := by
  constructor
  · intro h
    calc
      t % K = (ETC.exploreArm spec t).val := by
        rw [← ETC.exploreArm_val spec t]
      _ = a.val := by
        exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    simpa [ETC.exploreArm_val] using h

If namespace resolution is brittle, fully qualify:

lean
BanditRLProof.ETC.exploreArm

only where needed.

Do not weaken the theorem to one direction unless the iff genuinely reveals an API problem.

Do not import Finset, Mathlib tactics, probability, concentration, or the project root.

Do not start the m * K count theorem in the same batch.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

9. Minimal batch

Complete only:

ETC-EXPLOREARM-EQ-IFF-MOD

with:

one theorem near ETC.exploreArm
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should target the multiple full-cycle count theorem:

lean
pullCount (ETC.exploreArm spec) a (m * K) = m

or an equivalent orientation that matches local multiplication simplification.