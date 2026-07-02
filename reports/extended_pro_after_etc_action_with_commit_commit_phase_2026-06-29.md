I’ll keep this at the ETC trace/count boundary: the next leaf should transfer exploration-prefix pull counts from exploreArm to actionWithCommit, avoiding regret, probability, and commit selection.

Thought for 3m 30s
1. Next single executable leaf

Do the exploration-prefix pull-count transfer for ETC.actionWithCommit.

Recommended row:

ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT

Recommended theorem:

lean
ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le

This is the right next leaf because the phase-boundary API is now complete:

lean
ETC.actionWithCommit_eq_exploreArm_of_lt
ETC.actionWithCommit_eq_commitArm_of_ge

The next useful fact is that, on any prefix contained inside the exploration horizon, the fixed-commit trace has the same pull counts as the pure round-robin exploration trace.

Do not prove regret facts yet. Do not define empirical means or commit argmax. Do not touch probability or concentration.

2. Why this instead of a generic phase-splitting helper?

A generic phase-splitting helper would be useful later, but this pull-count transfer is the immediate dependency needed for ETC count and regret scaffolds.

It gives the exact bridge:

actionWithCommit agrees with exploreArm on all t < n
  =>
pullCount actionWithCommit a n = pullCount exploreArm a n

under the concrete condition:

lean
n <= spec.explorationPulls * K

That is more useful than a generic Boolean/if splitting theorem at this point.

3. File placement

Use a new small file:

BanditRLProof/Algorithms/ETCTraceCountLemmas.lean

Then import it from:

lean
BanditRLProof.lean

Reason: this theorem is no longer just a trace simplification, but it is also not yet a regret theorem. Keeping trace-count facts separate from ETCTrace.lean and ETCRegretLemmas.lean keeps the dependency graph clean.

4. Imports

Use:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace

These provide:

lean
pullCount_succ
ETC.actionWithCommit
ETC.actionWithCommit_eq_exploreArm_of_lt

No Mathlib import should be needed beyond transitive Nat basics.

Do not import:

lean
BanditRLProof.Algorithms.ETCCountLemmas
BanditRLProof.Algorithms.ETCRegretLemmas
BanditRLProof.RegretCountBounds
MeasureTheory
ENNReal
Probability
Concentration
Filtration
5. Exact Lean-facing statement
lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace

namespace BanditRLProof

theorem ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    pullCount (ETC.actionWithCommit spec commitArm) a n =
      pullCount (ETC.exploreArm spec) a n := by
  revert hn
  induction n with
  | zero =>
      intro hn
      simp [pullCount]
  | succ n ih =>
      intro hn
      have hn_le : n <= spec.explorationPulls * K :=
        Nat.le_trans (Nat.le_succ n) hn
      have hn_lt : n < spec.explorationPulls * K :=
        Nat.lt_of_succ_le hn
      have hact :
          ETC.actionWithCommit spec commitArm n = ETC.exploreArm spec n :=
        ETC.actionWithCommit_eq_exploreArm_of_lt spec commitArm hn_lt
      rw [pullCount_succ, pullCount_succ]
      rw [ih hn_le]
      rw [hact]

end BanditRLProof

If the last rewrite leaves a trivial Nat/if goal, close with:

lean
      simp

after rw [hact].

6. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm a : Fin K)
(n : Nat)
(hn : n <= spec.explorationPulls * K)

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

The positivity condition is already inside:

lean
spec.hK : 0 < K

No explicit decidability/finiteness assumptions should be necessary.

7. Local APIs to use

Use exactly:

lean
pullCount_succ
ETC.actionWithCommit_eq_exploreArm_of_lt

Do not use:

lean
ETC.actionWithCommit_eq_commitArm_of_ge
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
pseudoRegret
RegretCountBounds
Expectation*

The commit-phase theorem remains important for later suffix/count-after-commit facts, but it is not needed for this prefix-transfer leaf.

8. Classification

Classify this as:

ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT:
  project-local compiled ETC deterministic trace/count transfer

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC regret theorem

It is a project-local executable bridge supporting later:

ETC actionWithCommit exploration-horizon count
ETC full-trace count decomposition
ETC deterministic regret scaffold
9. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm the new file imports:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace

If the induction does not generalize hn, keep the explicit:

lean
revert hn

before the induction.

If Nat.lt_of_succ_le does not elaborate, replace the proof of hn_lt with:

lean
exact Nat.lt_of_succ_le hn

or inspect the local Nat lemma name before changing the theorem.

If rw [pullCount_succ, pullCount_succ] rewrites too aggressively, use a calc block and instantiate the recurrence explicitly.

If the final rw [hact] does not close, add:

lean
simp [hact]

Do not prove the exploration-horizon count theorem in the same batch.

Do not prove regret facts, empirical means, commit argmax, probability, concentration, filtration, or final ETC theorem facts in this batch.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

10. Minimal batch

Complete only:

ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT

with:

BanditRLProof/Algorithms/ETCTraceCountLemmas.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next likely leaf is the exploration-horizon count for the phase-switching trace:

lean
pullCount (ETC.actionWithCommit spec commitArm) a
  (spec.explorationPulls * K)
=
spec.explorationPulls