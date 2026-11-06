# First expansion: sealed authoring scope

Base and library: `abc2959ff7c866c47e8bee5714d43a336a857353`. Author: Codex /root. Source is the repository's MIT
finite-sum and finite-horizon interfaces, not a claim to reproduce a book theorem.
Inventory: four legacy cores (regret accounting, expected regret, confidence
schedules, estimator semantics); no submitted task packages; open GitHub search
for BanditRLBench proposals returned none on 2026-11-06. Search inspected
Exp3ImportanceWeighted, Exp3ConditionalMoments, FiniteHorizonMDP,
FiniteHorizonPolicy and FiniteHorizonOptimality plus the Mathlib induction/sum API.

Outcome: a benchmark integration node with two public-dev families and six tasks.
Reuse decision: adapt existing interfaces; no new production declaration or
per-book project. Targets are fixed in each Lean task's target.json before proof
execution. Task seals bind the complete question and environment. Reference
files are outside agent-visible inputs. Exact sources and graph IDs are in each
task.json; these are source-correspondence overlays. Compiled reference constants
will be reported separately, never inferred from imports.

Binder audit A: Action/DecidableEq are TYPING; finite arms, functions, action
membership, normalization and nonzero selected probability are SOURCE premises
of the original algebra question. Nonnegative weights and bounded losses belong
to the NL probability view, not to the more general algebra target. No EXCESS.
Binder audit B: finite types/measurable spaces are TYPING/standing library
structure; mdp/policy/v, terminal data, recurrence and valid stage are SOURCE
premises of a uniqueness question. The recurrence is not smuggled in as a
premise of an existence or trajectory-return theorem. No EXCESS.

Source proof coverage: A uses finite coordinate cancellation, a derived second
moment, square expansion and normalization. B uses terminal data, chronological
recursion and backward induction. Conditional-law transport and optimality are
context-only/excluded from the formal subtargets. No new source correction.

Separate actors will decode only the sealed targets, then review source versus
decoding and all NL rubrics. Their agent reviews do not replace independent human
expert gold admission. Reader index will show draft status and per-gate evidence.
Lean Graph: reuse-only. Overview: benchmark proposal index only. Functor: none
found with reason (no new formal transport). Teaching, results and route closure
statuses do not change. Existing process-memory atomic-assumption and Windows
environment lessons were consulted; no scheduler policy changes.

Independent inventory correction: the source reviewer found
`BanditRLProof.Exp3.sum_prob_mul_sq_comparatorEstimatorDeviation_eq` in
`BanditRLProof/Exp3ComparatorBernstein.lean` at the pinned source. This is a
near-complete solution alias: its `FiniteActionDistribution` premise adds
nonnegativity, while the proof uses only normalization. All IW views and the
family inventory now record it. The formal task is retrieval/adaptation with
unmeasured difficulty; no independent-synthesis or unseen-evaluation claim.
Legacy `estimator-semantics` is a related public-dev family, not an alternate
answer to the centered-moment task. Both remain publicly exposed.

Local execution correction: the initial full check compiled the root and Tests
but Python tests hit GBK decoding and one Git/LF declaration-boundary hash in the
CRLF checkout. UTF-8 mode and restoring that untouched file's exact Git bytes
resolve the environmental causes; no production source/metadata change is made.
