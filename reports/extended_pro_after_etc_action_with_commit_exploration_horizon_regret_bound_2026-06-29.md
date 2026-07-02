The next step should stay concrete: prove the first post-exploration one-step count recurrence for actionWithCommit, not a generic suffix helper.

1. Next single executable leaf

Do the first post-exploration commit-arm count increment lemma.

Recommended row:

ETC-ACTION-WITH-COMMIT-COMMITARM-SUCC-COUNT

Recommended theorem:

lean
ETC.pullCount_actionWithCommit_commitArm_succ_of_ge

This is smaller than a generic suffix-count helper and directly uses the compiled commit-phase boundary:

lean
ETC.actionWithCommit_eq_commitArm_of_ge

It establishes the local recurrence needed for later suffix counts:

after exploration, each additional round increments the committed arm’s count by one

Do not prove the full suffix formula yet.

2. Exact Lean-facing statement

Add this theorem to:

BanditRLProof/Algorithms/ETCTraceCountLemmas.lean

Statement:

lean
namespace BanditRLProof

theorem ETC.pullCount_actionWithCommit_commitArm_succ_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (ht : spec.explorationPulls * K <= t) :
    pullCount (ETC.actionWithCommit spec commitArm) commitArm (Nat.succ t) =
      pullCount (ETC.actionWithCommit spec commitArm) commitArm t + 1 := by
  rw [pullCount_succ]
  have hact :
      ETC.actionWithCommit spec commitArm t = commitArm :=
    ETC.actionWithCommit_eq_commitArm_of_ge
      (spec := spec)
      (commitArm := commitArm)
      (t := t)
      ht
  simp [hact]

end BanditRLProof

Use Nat.succ t, not t + 1, because it aligns directly with the existing local recurrence:

lean
pullCount_succ

A later convenience theorem can expose the t + 1 shape if needed.

3. Imports and local APIs

The existing file should already have enough:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace
import BanditRLProof.Algorithms.ETCCountLemmas

This theorem only needs:

lean
pullCount_succ
ETC.actionWithCommit_eq_commitArm_of_ge

It does not need:

lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
RegretCountBounds
ETCRegretLemmas
MeasureTheory
ENNReal
Probability
Concentration
Filtration

If the current file already imports ETCCountLemmas for the exploration-horizon count theorem, leave it. Do not add new imports for this leaf.

4. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm : Fin K)
{t : Nat}
(ht : spec.explorationPulls * K <= t)

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
empirical mean assumptions
concentration assumptions

The positivity condition is already contained in:

lean
spec.hK : 0 < K

No explicit decidability assumption should be necessary.

5. Classification

Classify this as:

ETC-ACTION-WITH-COMMIT-COMMITARM-SUCC-COUNT:
  project-local compiled ETC deterministic trace/count recurrence

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC theorem

It is a project-local executable prerequisite for:

post-exploration commit-arm count formula
full actionWithCommit count decomposition
deterministic ETC regret scaffold past exploration
6. Why this before a generic suffix-count helper?

A generic suffix helper would be useful later, but this recurrence is the concrete local fact needed first. It is also very small:

commit phase equality
  + pullCount_succ
  =
commit-arm count increments by one

Once this compiles, a later theorem can prove:

lean
pullCount (ETC.actionWithCommit spec commitArm) commitArm
  (spec.explorationPulls * K + r)
=
spec.explorationPulls + r

by induction on r.

7. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm ETCTraceCountLemmas.lean imports:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace

If pullCount_succ does not rewrite the goal, use an explicit calc:

lean
calc
  pullCount (ETC.actionWithCommit spec commitArm) commitArm (Nat.succ t)
      =
    pullCount (ETC.actionWithCommit spec commitArm) commitArm t
      + if ETC.actionWithCommit spec commitArm t = commitArm then 1 else 0 := by
        rw [pullCount_succ]
  _ =
    pullCount (ETC.actionWithCommit spec commitArm) commitArm t + 1 := by
        have hact :
            ETC.actionWithCommit spec commitArm t = commitArm :=
          ETC.actionWithCommit_eq_commitArm_of_ge
            (spec := spec)
            (commitArm := commitArm)
            (t := t)
            ht
        simp [hact]

If theorem namespace resolution is brittle, fully qualify:

lean
BanditRLProof.ETC.actionWithCommit_eq_commitArm_of_ge

Do not change the public hypothesis from ≤ to ¬ <. The ≤ version is the right downstream interface.

Do not prove the non-commit-arm no-increment theorem in the same batch.

Do not prove full suffix count, regret facts, empirical means, commit argmax, probability, concentration, filtration, or final ETC theorem facts in this batch.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Minimal batch

Complete only:

ETC-ACTION-WITH-COMMIT-COMMITARM-SUCC-COUNT

with:

one theorem in BanditRLProof/Algorithms/ETCTraceCountLemmas.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next likely leaf is either the non-commit-arm post-exploration no-increment lemma or the full commit-arm suffix-count formula.

Thought for 2m 44s
1. Next single executable leaf

Do the first post-exploration one-step pull-count update for ETC.actionWithCommit.

Recommended row:

ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT

This should not be a full suffix-count theorem yet. Prove only the one-step recurrence after the exploration horizon. That gives the exact local primitive needed later for closed-form suffix counts.

2. Exact Lean-facing statement

Add this theorem to:

BanditRLProof/Algorithms/ETCTraceCountLemmas.lean

Recommended theorem:

lean
theorem ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) {t : Nat}
    (ht : spec.explorationPulls * K <= t) :
    pullCount (ETC.actionWithCommit spec commitArm) a (Nat.succ t) =
      pullCount (ETC.actionWithCommit spec commitArm) a t +
        if commitArm = a then 1 else 0 := by
  rw [pullCount_succ]
  have hact :
      ETC.actionWithCommit spec commitArm t = commitArm :=
    ETC.actionWithCommit_eq_commitArm_of_ge spec commitArm ht
  simp [hact]

This is better than proving only the a = commitArm specialization, because it captures both cases:

lean
commitArm = a     -- count increments by 1
commitArm ≠ a     -- count stays fixed

but it is still only a one-step post-commit lemma, not a generic suffix decomposition.

3. Imports and local APIs

The existing imports in ETCTraceCountLemmas.lean should be enough. The theorem uses:

lean
pullCount_succ
ETC.actionWithCommit_eq_commitArm_of_ge

So the relevant imports are already:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace

If the file currently also imports:

lean
import BanditRLProof.Algorithms.ETCCountLemmas

that can remain because the previous horizon-count theorem needs it.

Do not add imports for:

lean
RegretCountBounds
ETCRegretLemmas
MeasureTheory
ENNReal
Probability
Concentration
Filtration
Conditional expectation
4. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm a : Fin K)
{t : Nat}
(ht : spec.explorationPulls * K <= t)

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
empirical mean assumptions
concentration assumptions

spec.hK : 0 < K is already inside ETC.Spec K, and decidable equality for Fin K should synthesize.

5. Classification

Classify this as:

ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT:
  project-local compiled ETC deterministic trace/count update

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC theorem

It is a local executable scaffold for later:

post-exploration commit-arm count closed form
non-commit-arm count stability
full actionWithCommit pull-count decomposition
6. Why not a generic suffix-count helper now?

A closed-form suffix theorem would likely need a second induction and case split on commitArm = a, for example:

lean
pullCount (ETC.actionWithCommit spec commitArm) a
  (spec.explorationPulls * K + r)
=
spec.explorationPulls + if commitArm = a then r else 0

That is the right direction later, but this one-step theorem is the smaller reusable primitive. It also tests that the commit-phase simplifier and pullCount_succ interact cleanly.

7. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm ETCTraceCountLemmas.lean imports:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace

If the final simp [hact] does not close, use an explicit case split:

lean
rw [pullCount_succ]
have hact :
    ETC.actionWithCommit spec commitArm t = commitArm :=
  ETC.actionWithCommit_eq_commitArm_of_ge spec commitArm ht
by_cases h : commitArm = a
· simp [hact, h]
· simp [hact, h]

If pullCount_succ does not rewrite Nat.succ t, inspect the local recurrence orientation and use the matching successor form. Do not change the theorem statement unless necessary.

Do not prove the full suffix-count closed form in this batch.

Do not add regret, empirical mean, argmax, probability, concentration, filtration, conditional expectation, or final ETC theorem facts.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Minimal batch

Complete only:

ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT

with:

one theorem in BanditRLProof/Algorithms/ETCTraceCountLemmas.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next likely leaf is the closed-form post-exploration count theorem over a suffix length r.

2/2