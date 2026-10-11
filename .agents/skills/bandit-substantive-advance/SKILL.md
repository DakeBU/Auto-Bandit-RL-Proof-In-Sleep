# BanditRLlib substantive advance

Read `docs/proof-digestion-protocol.md` and `docs/evidence-routed-memory-protocol.md` before source-facing proof work.
A substantive advance is one bounded mathematical or publication delta that changes the maintained theorem/route graph.

## Before work

For a new or materially changed source-facing Anchor, first complete the Statement Seal. New source-facing manifests should use contribution-contract schema 3.0 and fill `learning_contract`. Consult curated process/negative memory before dispatch; the control plane may choose the next process but may not invent mathematical conclusions. Expand project-owned assumption bundles, reject `EXCESS` binders, and keep every proof ingredient as a dependency edge rather than a new public premise. Reconstruct source proof topology independently of implementation Lean; every substantive source region is `NODE` or `EXCLUDED(reason)`, missing bridges are `SOURCE_GAP`, and alternative sufficient proofs are OR-routes.

Return:

- source anchor;
- theorem-sized target;
- route/frontier owner;
- owning Lean files/declarations;
- semantic fingerprint;
- BanditRLlib/Mathlib/LML/upstream search;
- reuse decision;
- reader publication delta;
- semantic round-trip plan;
- route/progress delta;
- Lean/Overview/Functor graph delta.

## Success outcomes

Exactly one of:

- `theorem-edge`;
- `reusable-interface`;
- `integration-node`;
- `source-correction`;
- `strict-obstruction`.

Raw helper count, commits, prompts, or branches are not mathematical progress.

## Shared-floor rule

If a missing lemma has at least two real consumers, prefer one shared declaration. Near-equivalent statements should share the common core and keep explicit adapters for different assumptions/conventions.

## Publication output

Create/update a contribution contract with:

```yaml
id:
route:
frontier_cell:
source_facing:
source:
target:
affected_files: []
declarations: []
reuse_plan:
reader_contract:
semantic_roundtrip:
graph_contribution:
  lean_graph:
  overview_graph:
  functor_hypergraph:
learning_contract:
  control_plane_math_authority: false
  process_memory_checked: true
  process_memory_ids: []
  failure_class: NONE | REFUTED | SOURCE_INVALID | API_BLOCKED | ENV_BLOCKED | IMPLEMENTATION_FAILED
  salvage:
    required: false
    status: not-applicable | pending | completed
    reason:
    promoted_fragments: []
    discarded_fragments: []
  parallelism:
    decision: serial | parallel
    direction_fingerprints: []
    expected_information_gain:
    shared_verified_context_digest:
  cross_route_blind_spot_audit:
    required: false
    status: not-applicable | pending | accepted
    evidence:
    canonical_route:
    selection_reason:
  reader_backpressure:
    purification_status: pending | purified | not-applicable
    exposition_seal_status: pending | accepted | not-applicable
    reader_debt_delta: 0
    exposition_evidence:
    source_expansion_nodes: []
    lean_expansion_nodes: []
    assumptions_preserved: false
    boundary_preserved: false
progress_updates:
truth_boundary:
verification:
contributor:
```

### Reader contract
For source-facing theorems all of:
- source anchor visible;
- natural-language formula proof;
- hidden assumptions visible;
- source-vs-Lean delta visible;
- exact Lean folded;
- actual dependencies visible;
- remaining boundary visible.

### Graph contribution
- Lean: `new-node | reuse-only | integration-node | no-change-with-reason`
- Overview: `updated | no-change-with-reason`
- Functor: `none-found-with-reason | candidate-published | stabilized`

## Blocker discipline

A blocked result must identify the exact obstruction and strictly reduce the next boundary. Before scheduling, classify it as REFUTED / SOURCE_INVALID / API_BLOCKED / ENV_BLOCKED / IMPLEMENTATION_FAILED. Every non-NONE failure receives an explicit salvage audit. API/environment/implementation failures may not retire the mathematical target. Multiple serious parallel routes require distinct direction fingerprints and a common-blind-spot review.

## Stabilization and purification

Rebase/clean-port current main; update shared imports/tests, canonical route/progress data, source mapping, Source Proof Graph, Lean Graph, candidate Compressed Bandit/RL Spine, Functor Hypergraph, reader pages, and contributor credit only where affected.

After merge, `MERGED` remains an integration state. Do not call a source route fully digested until the purification pass has removed dead/duplicate/wrapper-only residue, canonicalized reusable primitives, compressed bookkeeping while retaining drill-down evidence, and marked the result `PURIFIED`.

Run the contract, Lean, site, and diff gates before merge.
