I’ll keep this to one executable local leaf: introduce a fixed-commit ETC phase-switching trace boundary and prove only its exploration-prefix agreement, without empirical-mean or final-regret logic.

Thought for 3m 11s
1. Next single executable leaf

Define the first phase-switching ETC action trace boundary, but keep it commit-arm-parametric.

Recommended row:

ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE

This should introduce a deterministic ETC trace that explores by round-robin until the configured exploration horizon and then commits to an externally supplied arm:

lean
spec.explorationPulls * K

Do not introduce empirical means, argmax selection, probability, concentration, or final ETC regret yet. The commit arm should be an explicit parameter:

lean
commitArm : Fin K

This gives later work a stable boundary without forcing the empirical-mean/argmax design now.

2. Exact Lean-facing definition and theorem

Create a new file:

BanditRLProof/Algorithms/ETCTrace.lean

with:

lean
import BanditRLProof.Core
import BanditRLProof.Algorithms.ETC

namespace BanditRLProof

namespace ETC

def actionWithCommit
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) :
    ActionTrace (Fin K) :=
  fun t : Nat =>
    if t < spec.explorationPulls * K then
      ETC.exploreArm spec t
    else
      commitArm

@[simp] theorem actionWithCommit_eq_exploreArm_of_lt
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : t < spec.explorationPulls * K) :
    ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t := by
  simp [ETC.actionWithCommit, h]

end ETC

end BanditRLProof

This is intentionally only the exploration-side boundary. The commit-side theorem should be the next leaf, not part of this batch.

3. Why this before more deterministic ETC regret scaffolds?

You already have the exploration-only regret scaffold:

lean
ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls

The missing object is now the trace that future ETC lemmas can reference. Defining it with an explicit commitArm gives a local API for later statements such as:

lean
ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t

during exploration, and:

lean
ETC.actionWithCommit spec commitArm t = commitArm

after exploration.

That is the correct boundary before proving pull-count or regret facts about the phase-switching trace.

4. Imports and local APIs

Use only:

lean
import BanditRLProof.Core
import BanditRLProof.Algorithms.ETC

Local APIs used:

lean
ActionTrace
ETC.Spec
ETC.exploreArm

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

This leaf should not depend on count or regret lemmas. It is a trace-construction boundary.

5. Regularity contracts

The definition and theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm : Fin K)

and, for the theorem:

lean
h : t < spec.explorationPulls * K

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

The condition 0 < K is already carried by:

lean
spec.hK : 0 < K

inside ETC.Spec K.

6. Classification

Classify this as:

ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE:
  project-local compiled ETC trace-boundary leaf

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC regret theorem

It is a project-local executable boundary supporting future leaves:

ETC-ACTION-WITH-COMMIT-COMMIT-PHASE
ETC pull-count after exploration
ETC deterministic full-trace regret scaffold
empirical-argmax commit trace later
7. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm the new file imports:

lean
import BanditRLProof.Core
import BanditRLProof.Algorithms.ETC

If ActionTrace is already exported through another local file, keeping the explicit Core import is still acceptable. Do not import the project root.

If namespace elaboration is brittle, write the theorem outside the nested namespace:

lean
theorem ETC.actionWithCommit_eq_exploreArm_of_lt ...

with the same body.

If simp [ETC.actionWithCommit, h] does not close, use:

lean
unfold ETC.actionWithCommit
simp [h]

Do not prove the commit-phase theorem in this batch.

Do not prove pull-count or regret facts about actionWithCommit in this batch.

Do not introduce empirical means, commit argmax, probability, concentration, filtration, or final ETC regret.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Minimal batch

Complete only:

ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE

with:

BanditRLProof/Algorithms/ETCTrace.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next likely leaf is the complementary commit-phase theorem:

lean
@[simp] theorem ETC.actionWithCommit_eq_commit_of_not_lt
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : ¬ t < spec.explorationPulls * K) :
    ETC.actionWithCommit spec commitArm t = commitArm

or the equivalent spec.explorationPulls * K <= t version.