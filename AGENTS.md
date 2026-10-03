# Agent Guide for BanditRLlib / ABRL

This repository is a Lean-first formalization of Bandit and reinforcement-learning theory. Every mathematical contribution must preserve four things at once:

1. the exact source boundary;
2. compiler-backed Lean truth;
3. a reader-facing natural-language/LaTeX explanation;
4. the contribution's position in the route, progress ledger, Lean Graph, and conceptual Functor Hypergraph.

A compiling theorem is not automatically a faithful source theorem, a completed route, or a new conceptual bridge.

## Read before editing

Every collaborator and every Codex/ChatGPT/Claude agent acting for a collaborator must read, in this order:

1. `AGENTS.md`
2. `CONTRIBUTING.md`
3. `docs/contributor-codex-contract.md`
4. `docs/theorem-publication-protocol.md`
5. `.agents/skills/bandit-substantive-advance/SKILL.md`
6. `.agents/skills/bandit-semantic-roundtrip/SKILL.md`
7. the relevant domain skill under `.agents/skills/`
8. the exact route/source files being changed.

Repository-local instructions override copied prompts from chat.

## Non-negotiable project gate

```bash
python3 tools/bandit.py check
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
```

For a contribution PR, also run the contributor contract against the PR base:

```bash
python3 tools/check_contributor_contract.py --base BASE_COMMIT
```

No `sorry`, `admit`, hidden axiom closure, fake theorem wrapper, hand-edited completion badge, or generated `website/_site/` output may be used to close mathematics.

## Unit of work: one bounded mathematical advance

A substantive contribution should close one theorem edge, reusable interface, integration node, source correction, or strict obstruction. Before coding, record:

- exact source paper/book/version/theorem anchor;
- exact theorem-sized target and route;
- existing BanditRLlib / Mathlib / compatible external declarations searched;
- reuse decision: `reuse_existing | adapt_existing | new_route_local | new_shared | out_of_scope`;
- owning Lean module and downstream consumers;
- reader/publication delta;
- semantic encoder–denoiser plan;
- route/progress delta;
- Lean Graph / Overview Graph / Functor Hypergraph delta.

If a lower-level lemma has at least two real consumers, prefer one canonical shared declaration plus explicit adapters instead of route-local duplication.

## Source and reader publication contract

Every new or changed source-facing production declaration follows `docs/theorem-publication-protocol.md`.

The reader-facing page must keep the following adjacent and in mathematical order:

1. attributed source statement or faithful restatement, with edition/version and anchor;
2. notation and explicit/hidden assumptions;
3. readable natural-language proof with displayed formulas;
4. source assumptions versus actual Lean assumptions;
5. exact Lean statement in a folded disclosure;
6. exact Lean proof in a folded disclosure when the site exposes proof text;
7. BanditRLlib parents actually reused;
8. Mathlib/LML/external facts actually used;
9. the remaining red boundary: what is not proved.

Do not replace this with a code dump, status table, or theorem inventory.

## Mandatory semantic round trip

Lean compilation checks a proposition, not fidelity to a cited theorem.

For every source-facing theorem, perform the encoder–denoiser round trip from `.agents/skills/bandit-semantic-roundtrip/SKILL.md`:

`source -> Lean statement -> source-blind reconstruction -> independent anti-anchored source review`.

The formalizer, blind decoder, and source reviewer must be distinct actors. A proposed source repair is stored separately from the pinned source and requires separate review. Never silently strengthen assumptions or mutate a faithful source target for API convenience.

## Three graph truth contracts

Every substantive contribution must classify all three views.

### Lean Graph

Compiler-backed module/declaration structure and reviewed proof dependencies. Formal structure is solid. Imports alone do not imply theorem implication. Planned consumers, source correspondence, semantic similarity, and conceptual mirrors are overlays, not solid theorem edges.

### Overview / route-progress graph

Records where books, settings, source routes, frontier problems, milestones, and formalization status live. Updating one theorem may change a route without completing the route or chapter. Progress badges are generated from canonical data and are never hand-edited.

### Functor Hypergraph

Records recurring mathematical mechanisms across settings after changing the space, feedback model, objective, divergence, oracle, or state representation. A contribution must say one of:

- `none-found-with-reason`;
- `candidate-published`;
- `stabilized`.

A bridge requires stable IDs plus domains, formula/skeleton, mechanism, hypothesis map, conclusion map, source evidence, candidate Lean substrates, and a failure boundary. Conceptual similarity is dashed and never becomes a formal Lean edge or a certified functor without a separate proof certificate.

Canonical data:
- `website/content/functor_hypergraph.json`
- `website/content/graph_memory_index.json`

## Special cross-library settings

Some settings change the information model enough that another formal library should
supply part of the semantics rather than ABRL rebuilding it locally.

For `quantum-bandits`, read
`docs/quantum-bandit-cross-library-protocol.md` before defining any quantum
state, channel, oracle, measurement, or query-complexity interface. Search
BanditRLlib for the classical decision skeleton, then ASPBE/QuantumComputinglib
and its audited quantum Lean references for quantum semantics. External/cross-
library facts remain dashed candidate substrates until a compatible import,
local re-proof, or compiled adapter establishes an ABRL-owned theorem edge.

The same pattern applies to future cross-library routes: reuse the owning
library's foundations, preserve license/toolchain provenance, and formalize the
smallest explicit adapter instead of forking a second foundational library.

## Route and progress synchronization

A theorem contribution is incomplete as repository integration if the reader-facing project state remains stale. Update only affected canonical sources, but explicitly classify each surface:

- textbook/teaching route;
- BanditRLwiki case/setting/frontier history;
- `website/content/results.json` milestone status;
- roadmap/frontier route metadata;
- Lean Graph;
- Functor Hypergraph;
- source/provenance ledger;
- contributor credit.

`no-change-with-reason` is acceptable when a surface is genuinely unaffected. Silence is not.

## Collaboration safety

Exploration code should avoid rewriting shared registries from stale branches. Rebase or clean-port before stabilization. Shared metadata is merged semantically.

Only stabilization should update global publication/graph/progress truth after the mathematical target has focused evidence. Do not overwrite another contributor's registry or append-only work with an old snapshot.

## Honest states

Keep at least these notions independent:

- literature/source status;
- local Lean compilation status;
- semantic source-fidelity review;
- route/chapter completion;
- conceptual-hypergraph status;
- merge/integration status.

A local compiling helper is not a paper theorem. A paper theorem is not a minimax closure unless the assumptions match. A conceptual bridge is not a Lean dependency.

## Required contribution manifest

Substantive PRs carry one or more JSON manifests in
`research-wiki/contribution-contracts/`, validated by
`tools/check_contributor_contract.py`.

The manifest names changed production files, source anchor, route, declarations, reuse plan, reader contract, semantic audit, graph deltas, progress/site surfaces, remaining boundary, verification evidence, and contributor identity.

## Failure policy

Repeated failure is information. Stop blind tactic search when the same route fails repeatedly. Return a typed obstruction: false/missing assumption, representation mismatch, measurability/integrability gap, source ambiguity, incompatible upstream API, or target too large. Shrink the next theorem boundary explicitly.

"Lean failed" and "more work remains" are not acceptable final blocker descriptions.

## Minimal Codex bootstrap

Use `.agents/prompts/collaborator-contribution.md`. Its role is only to point Codex to the current repository contract; it is not a second copy of these rules.
