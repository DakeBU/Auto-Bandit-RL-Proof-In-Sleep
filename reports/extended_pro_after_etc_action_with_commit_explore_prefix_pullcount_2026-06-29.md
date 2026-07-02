Thought for 1m 43s
1. Next single executable leaf

Yes. The next leaf should be the exploration-horizon count theorem for ETC.actionWithCommit.

Recommended row:

ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT

Recommended theorem:

lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq

This is the direct consumer of the transfer theorem you just compiled plus the pure exploration horizon theorem.

2. Exact Lean-facing statement

Add this theorem to:

BanditRLProof/Algorithms/ETCTraceCountLemmas.lean

Statement:

lean
namespace BanditRLProof

theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) =
      spec.explorationPulls := by
  calc
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K)
        =
      pullCount (ETC.exploreArm spec) a
        (spec.explorationPulls * K) := by
          exact
            ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
              (spec := spec)
              (commitArm := commitArm)
              (a := a)
              (n := spec.explorationPulls * K)
              (hn := le_rfl)
    _ = spec.explorationPulls := by
          exact
            ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
              (spec := spec)
              (a := a)

end BanditRLProof

This should be a proof by composition only. Do not reprove the induction over pullCount.

3. Imports

Update ETCTraceCountLemmas.lean to import the pure ETC count theorem:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace
import BanditRLProof.Algorithms.ETCCountLemmas

This import is justified now. The new theorem depends on:

lean
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq

which lives in ETCCountLemmas.

The dependency direction is clean:

ETC.lean
  ↓
ETCCountLemmas.lean
  ↓
ETCTraceCountLemmas.lean

and:

ETC.lean
  ↓
ETCTrace.lean
  ↓
ETCTraceCountLemmas.lean

Do not import:

lean
BanditRLProof.Algorithms.ETCRegretLemmas
BanditRLProof.RegretCountBounds
MeasureTheory
ENNReal
Probability
Concentration
Filtration
4. Local APIs to use

Use exactly:

lean
ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq

Do not reopen:

lean
pullCount
pullCount_succ
ETC.actionWithCommit
ETC.exploreArm
ETC.pullCount_exploreArm_mul_K_eq

Those facts are already encapsulated by the two local APIs above.

5. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm a : Fin K)

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

The positivity contract remains inside:

lean
spec.hK : 0 < K
6. Classification

Classify this as:

ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT:
  project-local compiled ETC deterministic trace/count adapter

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC regret theorem

It supports later:

ETC full-trace count decomposition
ETC deterministic regret scaffold for actionWithCommit
pull_count_bound_after_commit
7. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm ETCTraceCountLemmas.lean imports:

lean
import BanditRLProof.Algorithms.ETCCountLemmas

If le_rfl does not elaborate for the horizon inequality, replace it with:

lean
(hn := Nat.le_refl (spec.explorationPulls * K))

If the calc proof is brittle, use a rw version:

lean
rw [ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
  (spec := spec)
  (commitArm := commitArm)
  (a := a)
  (n := spec.explorationPulls * K)
  (hn := le_rfl)]
exact ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
  (spec := spec)
  (a := a)

If namespace resolution is brittle, fully qualify the two reused theorem names.

Do not reprove the prefix-transfer theorem.

Do not prove regret facts in this batch.

Do not add empirical means, commit argmax, probability, concentration, filtration, conditional expectation, or final theorem work.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Minimal batch

Complete only:

ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT

with:

one theorem in BanditRLProof/Algorithms/ETCTraceCountLemmas.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to prove the first post-exploration commit-arm count increment lemma or a deterministic regret scaffold for actionWithCommit over the exploration horizon.