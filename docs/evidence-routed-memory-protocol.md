# Evidence-Routed Memory and Adaptive Scheduling Protocol

This protocol complements `docs/proof-digestion-protocol.md` and preserves
BanditRLlib's existing evidence-gated harness design. It adapts the useful
cross-round learning mechanisms of arXiv:2609.40324 without adding permanent
orchestrator/advisor/prover castes.

The core rule is:

> **Lean-verified lemmas are positive proof memory; checked counterexamples and
> source defects are negative mathematical memory; API/environment/process
> failures are routing evidence only.**

## 1. Typed failure classes

Every failed/rejected route is classified before it changes the proof frontier:

- `REFUTED`: the mathematical claim/route is ruled out by a checked
  counterexample or rigorous reviewed proof;
- `SOURCE_INVALID`: the pinned source statement, convention, or quantifier
  contract is false/ill-posed and needs source repair;
- `API_BLOCKED`: the theorem may be true but the current Lean/Mathlib/LML/API
  interface blocks this route;
- `ENV_BLOCKED`: filesystem, dependency, CI, path-length, package, or runtime
  environment blocked execution;
- `IMPLEMENTATION_FAILED`: one implementation/proof attempt failed without
  evidence that the mathematics is false;
- `NONE`: no failure.

Only `REFUTED` or independently reviewed `SOURCE_INVALID` evidence can retire
a mathematical route. The other three classes must never be rendered as
negative mathematical results.

## 2. Salvage before discard

A rejected or blocked proof route receives a salvage audit before its code is
deleted or its branch is retired. The audit asks whether the failed parent
contains independently useful:

- concentration/confidence lemmas;
- Bellman/occupancy identities;
- martingale/stopping results;
- information/change-of-measure facts;
- source counterexamples or statement repairs.

A candidate fragment is promoted only after isolation from route-local context,
assumption minimization, direct Lean compilation, axiom/source review as
appropriate, and the ordinary shared-node/reuse audit. Text copied from a failed
proof is not proof memory.

## 3. Preserve BanditRLlib's existing ledgers

Positive theorem memory remains:

- compiled BanditRLlib declarations;
- `runs/lifecycle_memory.jsonl` accepted/verified entries;
- current route/frontier/source ledgers.

Curated process/negative memory lives in `runs/process_memory.json` and is
validated by `tools/check_process_memory.py`.

The full `runs/trials.jsonl` remains debugging history, not prompt memory.
Only curated evidence-backed entries may become standing instructions.

## 4. Failure router, not mathematical advisor

The control plane has `control_plane_math_authority = false`. It may map a
typed error to the next **process**:

| Failure | Default next process |
| --- | --- |
| `REFUTED` | retire same sealed route; salvage; open a mathematically distinct route |
| `SOURCE_INVALID` | source audit / repair; freeze proof work on stale statement |
| `API_BLOCKED` | retrieval, adapter, or dependency/API lane |
| `ENV_BLOCKED` | deterministic infrastructure repair |
| `IMPLEMENTATION_FAILED` | retry only after route fingerprint or implementation plan changes |
| `NONE` | ordinary frontier scheduling |

It may not assert that optimism, coupling, information theory, or any other
unverified mathematical route is correct.

## 5. Parallelism remains evidence-gated

BanditRLlib already has an internal hierarchical versus master-worker matched
experiment protocol. This remains authoritative.

A scheduler default may not change merely because another project reports a
multi-agent win. The current repository requires at least the configured number
of **matched experiments** with the same target fingerprint, same frozen
route-packet hash, and reviewer-owned verdicts.

Within one theorem target, parallel workers are admitted only for distinct
`direction_fingerprint` values with independent uncertainty, such as:

- optimism/confidence versus information-theoretic proof routes;
- proof construction versus counterexample search;
- source/adaptivity audit versus Lean implementation;
- disjoint proof leaves with non-overlapping ownership.

Each worker receives the same Statement Seal and verified-memory digest, but
only route-specific failure history. Duplicating the whole trial log across
several workers is prohibited.

## 6. Common-blind-spot review for multiple routes

If two or more serious routes survive to verification, a separate side-by-side
reviewer looks for shared mistakes: hidden fixed horizon, filtration/adaptivity
drift, stronger feedback information, confidence-event conditioning, uniform
constant drift, or a common source misread.

This review is mandatory for a parallel multi-route source claim before proof
seal. It is not required for unrelated independent library leaves.

## 7. Evidence-bound standing instructions

A standing instruction may be promoted only from repeated or high-impact
repository evidence. Every instruction records evidence files/needles, scope,
and retirement condition.

Current evidence already justifies process lessons such as:

- do not change the default harness with zero matched A/B experiments;
- source-facing assumption metadata must remain atomic/Lean-facing rather than
  one opaque prose blob;
- Windows path-length failure is environment evidence, not theorem failure.

Standing instructions are compact prompt memory. They are never proof
dependencies.

## 8. Reader backpressure and Exposition Seal

Track proof-production debt separately from theorem correctness:

- merged source claims not yet PURIFIED;
- age of unpurified claims;
- fine proof nodes per reviewed conceptual move.

When this debt grows, scheduling must reserve capacity for proof digestion and
reader synthesis instead of sending all budget to new frontier claims.

A PURIFIED source-facing theorem requires an **Exposition Seal**: compressed
reader prose must expand to the correct source and Lean nodes, preserve
filtration/probability/feedback assumptions and the remaining boundary, and be
reviewable without knowing the agent run.

## 9. Contribution-contract version 3

New substantive source-facing work should use contribution-contract schema 3.0.
It adds a machine-readable `learning_contract` with:

- process-memory references;
- typed failure class;
- salvage status;
- serial/parallel admission evidence and direction fingerprints;
- common-blind-spot review;
- reader-backpressure and Exposition Seal state.

Historical 2.0 manifests remain valid; no old evidence is fabricated
retroactively.

## Design provenance

This protocol is informed by arXiv:2609.40324's attempt memory, verified lemma
memory, cross-round process learning, side-by-side verification, and final
writeup verification. BanditRLlib keeps its own stronger invariants: Lean is the
proof gate, target/harness comparison is matched and evidence-gated, and
coordination activity is never counted as mathematical progress by itself.
