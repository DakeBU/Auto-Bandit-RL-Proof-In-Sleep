# BanditRLlib substantive advance

Read `docs/proof-digestion-protocol.md` before source-facing proof work.
A substantive advance is one bounded mathematical or publication delta that changes the maintained theorem/route graph.

## Before work

For a new or materially changed source-facing Anchor, first complete the Statement Seal. Expand project-owned assumption bundles, reject `EXCESS` binders, and keep every proof ingredient as a dependency edge rather than a new public premise. Reconstruct source proof topology independently of implementation Lean; every substantive source region is `NODE` or `EXCLUDED(reason)`, missing bridges are `SOURCE_GAP`, and alternative sufficient proofs are OR-routes.

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

A blocked result must identify the exact obstruction and strictly reduce the next boundary. Examples: missing measurability producer, false statement under stated assumptions, change-of-measure mismatch, source ambiguity, unavailable API, or theorem too large.

## Stabilization and purification

Rebase/clean-port current main; update shared imports/tests, canonical route/progress data, source mapping, Source Proof Graph, Lean Graph, candidate Compressed Bandit/RL Spine, Functor Hypergraph, reader pages, and contributor credit only where affected.

After merge, `MERGED` remains an integration state. Do not call a source route fully digested until the purification pass has removed dead/duplicate/wrapper-only residue, canonicalized reusable primitives, compressed bookkeeping while retaining drill-down evidence, and marked the result `PURIFIED`.

Run the contract, Lean, site, and diff gates before merge.
