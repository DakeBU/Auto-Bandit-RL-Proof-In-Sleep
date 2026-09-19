# Contributing to BanditRLlib

BanditRLlib accepts teaching corrections, source mappings, reusable mathematical
infrastructure, theorem formalizations, frontier audits, and graph/publication
improvements. A contribution is complete only when its mathematical truth,
source fidelity, reader explanation, route/progress state, and graph placement
agree.

## Required read order for substantial work

Before planning or asking Codex/ChatGPT/Claude to edit the repository, pull the
current target branch and read:

1. `AGENTS.md`
2. `CONTRIBUTING.md`
3. `docs/contributor-codex-contract.md`
4. `docs/theorem-publication-protocol.md`
5. `.agents/skills/bandit-substantive-advance/SKILL.md`
6. `.agents/skills/bandit-semantic-roundtrip/SKILL.md`
7. the relevant domain skill and exact source/route files.

The reusable bootstrap for coding agents is
`.agents/prompts/collaborator-contribution.md`. Repository-local instructions
are authoritative over copied chat prompts.

## Before writing Lean

For a substantial result, open or update a proposal and identify:

- exact paper/book/version/theorem or section anchor;
- theorem-sized mathematical target and assumptions;
- intended route/frontier and owning Lean module;
- existing BanditRLlib, Mathlib, LML, and compatible upstream declarations
  searched;
- reuse decision: reuse, adapt, route-local, or genuinely shared;
- reader-facing publication delta;
- source-blind encoder–denoiser audit plan;
- affected teaching/BanditRLwiki/progress surfaces;
- Lean Graph, Overview Graph, and Functor Hypergraph delta.

Do not create a route-local helper when an existing canonical theorem is
semantically compatible. If a missing lower-level lemma has at least two real
consumers, prefer one shared declaration plus explicit adapters.

## Two machine-readable contribution layers

Small community proposals may use
`website/community/entries/<id>.json` with
`website/community/contribution.schema.json`.

Every **substantive repository contribution** also adds or updates a manifest in
`research-wiki/contribution-contracts/`, following
`docs/contribution-contract.schema.json`. This manifest binds the actual diff
to its source, route, declarations, reuse decision, reader contract, independent
semantic review, graph deltas, progress/site surfaces, remaining truth boundary,
verification evidence, and contributor credit.

The diff-aware gate is:

```bash
python3 tools/check_contributor_contract.py --base BASE_COMMIT
```

A substantive production/site/graph change without a covering changed manifest
fails closed.

## Source-facing theorem standard

Lean compilation certifies a proposition, not that it is the theorem cited in a
paper or book. For every source-facing theorem, follow
`.agents/skills/bandit-semantic-roundtrip/SKILL.md`.

The formalizer, source-blind decoder, and anti-anchored source reviewer must be
distinct actors. The reader must expose the source anchor, natural-language
formula proof, hidden assumptions, source-vs-Lean assumption differences,
folded exact Lean, actual dependencies, and remaining boundary.

A proposed source correction is separate from the pinned source theorem and
requires separate review. Never silently strengthen assumptions to make Lean or
an API convenient.

## Route, website, and graph synchronization

Every substantive contribution explicitly classifies affected surfaces:

- teaching/book route and source spine when relevant;
- BanditRLwiki setting/case/frontier history;
- results/milestone and roadmap state;
- declaration/implementation map;
- Lean Graph;
- Functor Hypergraph;
- provenance and contributor credit.

Only affected surfaces are changed, but an unaffected surface must be recorded
as `no-change-with-reason` rather than silently ignored.

Formal compiler-backed graph structure uses solid edges. Source, planned,
semantic, scan-derived, and conceptual overlays remain dashed. A conceptual
mirror in the Functor Hypergraph is never a Lean theorem edge or a certified
categorical functor unless separately formalized.

## Honest independent statuses

Do not collapse literature/source status, local Lean compilation, semantic
source review, route/chapter completion, Functor Hypergraph status, and merge
integration into one badge.

In particular:

- a compiling helper is not automatically a source theorem;
- a source theorem is not automatically a matched frontier result;
- many compiled dependencies do not automatically complete a route;
- a conceptual bridge may be useful even when no formal transport theorem
  exists.

`integrated` means merged to `main` after the required gates; it is not
assigned to an isolated branch.

## Verification before merge

At minimum:

```bash
python3 tools/check_contributor_contract.py --base BASE_COMMIT
python3 tools/bandit.py check
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
git diff --check
```

Use focused Lean checks while editing. Record the commands actually run and
inspect the affected generated route/graph page when publication or graph
metadata changed.

No `sorry`, `admit`, hidden axiom/interface closure, fake wrapper theorem,
hand-edited completion badge, or committed generated `website/_site/` may be
used to close mathematics.

## Credit and license

Community packets and substantive manifests retain contributor identity and the
specific contribution scope. Community credit does not automatically imply ABRL
paper authorship. Intentional contributions are licensed under the repository's
MIT License; contributors must have the right to submit the material.

Follow the [Code of Conduct](CODE_OF_CONDUCT.md) and
[Governance](GOVERNANCE.md).
