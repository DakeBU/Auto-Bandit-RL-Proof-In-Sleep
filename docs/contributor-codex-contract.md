# BanditRLlib contributor and Codex contract

This contract applies to humans and coding agents contributing mathematics, source mappings, theorem-facing website material, routes, or graph metadata.

## 1. Search and reuse before declaring

Before creating a production declaration:

1. freeze the exact source statement, assumptions, domains, constants, and conventions;
2. search BanditRLlib by semantic content, not only names;
3. search Mathlib and the pinned compatible Lean libraries used by this project;
4. inspect active route/frontier/proof obligations for a shared target;
5. classify the result as `reuse`, `adapt`, `missing`, or `out_of_scope`;
6. decide `reuse_existing`, `adapt_existing`, `new_route_local`, `new_shared`, or `out_of_scope`.

A new shared declaration must name at least two realistic consumers. Do not create wrappers only to inflate reuse counts.

The contribution manifest records `searched_existing`, exact reused declarations, new shared declarations, known/planned consumers, `no_duplicate_wrapper: true`, and a decision reason.

## 2. Reader quality is part of theorem publication

For source-facing results, the website must show the mathematics, not merely advertise the Lean artifact.

For every represented source statement, keep adjacent:

1. source statement / faithful attributed restatement and exact anchor;
2. notation and hidden assumptions;
3. natural-language formula proof;
4. source-vs-Lean assumption ledger;
5. folded exact Lean statement;
6. folded exact proof when available to the renderer;
7. local declarations actually reused;
8. Mathlib/LML/external dependencies actually used;
9. remaining mathematical boundary.

Author canonical data; do not hand-edit `website/_site/`.

If the contribution belongs to a teaching chapter, source spine chapter, BanditRLwiki case, frontier history, or extended setting, update that route's canonical data. If it does not, record `no-change-with-reason`.

## 3. Encoder–denoiser semantic audit is mandatory

Compilation does not establish source equivalence.

For every source-facing theorem:

- pin the source statement;
- pin the actual Lean statement;
- give the Lean statement, without source identity, to a distinct blind decoder;
- reconstruct mathematical meaning and assumptions from Lean only;
- give source + reconstruction + Lean statement to a distinct anti-anchored reviewer;
- record mismatches explicitly.

The formalizer cannot self-certify the decoder or source-review stages. A theorem with rejected or incomplete source fidelity may remain useful local mathematics, but it cannot be labelled as faithful source formalization.

Repairs are separate objects: source theorem, actual Lean theorem, semantic mismatch, proposed repaired theorem.

## 4. Three graph views must be classified

Every substantive contribution records `graph_contribution`.

### Lean Graph

Allowed classifications: `new-node`, `reuse-only`, `integration-node`, `no-change-with-reason`.

Solid edges are reserved for compiler-backed structure/reviewed formal dependency relations. Source mappings, planned consumers, semantic links, and conceptual bridges are dashed overlays.

### Overview / route-progress

Allowed classifications: `updated`, `no-change-with-reason`.

Update affected books, setting/frontier placement, result/milestone status, and route progress. Never hand-edit a completion percentage or badge.

### Functor Hypergraph

Allowed classifications:

- `none-found-with-reason`;
- `candidate-published`;
- `stabilized`.

A candidate recurring mechanism needs stable `family:`, `transport:`, or `concept:` IDs, source domains, formula or proof skeleton, mechanism, hypothesis map, conclusion map, source IDs, candidate local Lean substrates, and a failure boundary.

The creator may propose a conceptual mirror but should not be the only validator. A conceptual edge is never rendered as a solid Lean dependency.

## 5. Route, progress, and website synchronization

For each substantive change, explicitly classify:

- teaching/book route;
- source Chapter 13–17 spine if relevant;
- BanditRLwiki setting/case/frontier history;
- `website/content/results.json`;
- roadmap / named frontier;
- declaration/implementation map;
- Lean Graph;
- Functor Hypergraph;
- contributor credit and source attribution.

The rule is affected-surface synchronization, not "edit everything". Each unaffected surface receives a short reason in the manifest.

## 6. Status discipline

Keep these ledgers separate:

- `literature_status`;
- `source_audit_status`;
- `lean_status`;
- `semantic_review_status`;
- `route_status`;
- `functor_status`;
- `integration_status`.

Never infer one from another.

## 7. Collaboration and stabilization

Do not replace shared metadata from a stale branch. Rebase or clean-port and merge registries semantically.

Exploration workers should avoid editing unrelated global aggregators. The stabilization owner integrates root imports/tests, canonical result status, route metadata, graph views, and website surfaces.

Before merge, run:

```bash
python3 tools/check_contributor_contract.py --base BASE_COMMIT
python3 tools/bandit.py check
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
git diff --check
```

When the contribution changes graph/publication metadata, inspect the affected generated page/branch and record the visual review in the manifest/PR.

## 8. Required manifest

Each substantive PR adds/updates one or more
`research-wiki/contribution-contracts/*.json` files conforming to
`docs/contribution-contract.schema.json`.

The contract checker fails closed when changed production surfaces are not covered by a changed manifest.

## 9. PR disclosure

The PR must state the exact mathematical/source delta, reuse decision, remaining truth boundary, semantic round-trip status, reader-page delta, route/progress delta, Lean Graph delta, Functor Hypergraph delta, and commands actually run.

Generated site output is never committed.
