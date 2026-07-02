I’ll keep this to one trace-boundary theorem and avoid pulling count/regret machinery into the batch.

Thought for 2m 47s
1. Next single executable leaf

Yes. The next leaf should be the complementary commit-phase theorem.

Recommended row:

ETC-ACTION-WITH-COMMIT-COMMIT-PHASE

Recommended theorem:

lean
ETC.actionWithCommit_eq_commitArm_of_ge

This should complete the basic phase-boundary API for:

lean
ETC.actionWithCommit

without introducing pull counts, regret, empirical means, argmax selection, probability, or concentration.

2. Use ≤, not ¬ <, as the public statement

Use the public-facing condition:

lean
spec.explorationPulls * K <= t

rather than:

lean
¬ t < spec.explorationPulls * K

Reason: downstream ETC statements will naturally phrase the commit phase as “after the exploration horizon.” The ≤ form is easier to read and easier to use in later phase-splitting lemmas.

The proof can internally convert it with:

lean
not_lt_of_ge h

Do not add both versions in this batch. The ¬ < version can be a future helper only if Lean rewriting later needs it.

3. Exact Lean-facing statement

Add this theorem to the existing file:

BanditRLProof/Algorithms/ETCTrace.lean

Statement:

lean
namespace BanditRLProof

namespace ETC

@[simp] theorem actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm := by
  have hnot : ¬ t < spec.explorationPulls * K := not_lt_of_ge h
  simp [ETC.actionWithCommit, hnot]

end ETC

end BanditRLProof

A slightly shorter proof may also compile:

lean
@[simp] theorem actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm := by
  simp [ETC.actionWithCommit, not_lt_of_ge h]

Prefer the first form if the local simplifier is sensitive.

4. Imports and local APIs

No new imports should be needed. Keep the current file imports:

lean
import BanditRLProof.Core
import BanditRLProof.Algorithms.ETC

Use only:

lean
ETC.actionWithCommit

and the Nat order lemma:

lean
not_lt_of_ge

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
5. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm : Fin K)
{t : Nat}
(h : spec.explorationPulls * K <= t)

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
pullCount
empirical mean assumptions
concentration assumptions

The positivity condition remains carried by:

lean
spec.hK : 0 < K

inside ETC.Spec.

6. Classification

Classify this as:

ETC-ACTION-WITH-COMMIT-COMMIT-PHASE:
  project-local compiled ETC trace-boundary leaf

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC regret theorem

It completes the two basic phase simplification facts:

lean
ETC.actionWithCommit_eq_exploreArm_of_lt
ETC.actionWithCommit_eq_commitArm_of_ge
7. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm the theorem is in BanditRLProof/Algorithms/ETCTrace.lean, after the definition of:

lean
ETC.actionWithCommit

If the short proof fails, use the explicit hnot form:

lean
have hnot : ¬ t < spec.explorationPulls * K := not_lt_of_ge h
simp [ETC.actionWithCommit, hnot]

If namespacing is brittle, write the theorem outside the nested namespace with the fully qualified name:

lean
theorem ETC.actionWithCommit_eq_commitArm_of_ge ...

Do not change the public statement to ¬ t < ... unless the ≤ version is genuinely blocked.

Do not add the ¬ < companion theorem in the same batch.

Do not prove pull-count, regret, empirical mean, commit argmax, probability, concentration, filtration, or final ETC theorem facts in this batch.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Minimal batch

Complete only:

ETC-ACTION-WITH-COMMIT-COMMIT-PHASE

with:

one theorem in BanditRLProof/Algorithms/ETCTrace.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to prove the exploration-prefix pull-count transfer for actionWithCommit or add a phase-splitting helper for times below/above spec.explorationPulls * K.