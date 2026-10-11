# BanditRLlib theorem publication protocol

Applies to every new or changed source-facing production declaration and every theorem-facing source correction.

The purpose is to author mathematics once and project it consistently into the reader, route/progress views, and graphs.

## Pre-proof Statement Seal and source-topology gate

Every new or materially changed source-facing theorem/definition also follows
`docs/proof-digestion-protocol.md` before proof search. Seal the exact final Lean
signature first. Recursively expand project-owned assumption bundles and classify
each logical input as `SOURCE`, `STANDING`, `TYPING`, `RULED`, or `EXCESS`; any
`EXCESS` binder rejects the source Anchor. A concentration bound, confidence
event, Bellman identity, occupancy relation, stopping argument, coverage lemma,
or change-of-measure inequality needed by the proof is a dependency edge to be
proved/reused and applied inside the proof, not an extra public premise.

Definitions are audited as literal, characterized, or quotient/representative.
A characterized object cannot be implemented with a fallback/default branch;
where uniqueness is part of the source semantics, prove the true source-level
well-definedness theorem before classical choice and land the full
characterization theorem with the definition.

Independently reconstruct the **Source Proof Graph** from the cited source. Every
in-scope theorem, definition, reused display, citation, and substantive proof
paragraph is `NODE` or `EXCLUDED(reason)`; omitted bridges remain `SOURCE_GAP`
nodes and alternative sufficient proofs are explicit OR-routes. This view asks
"how did the source prove it?"; the Lean graph asks "what does the checked
implementation actually depend on?". They must not be conflated.

After proof sealing/publication, run purification: remove dead, duplicate and
wrapper-only proof residue, minimize/canonicalize imports and shared APIs,
compress bookkeeping into reviewed conceptual moves, preserve lossless drill-
down evidence, and update the Compressed Bandit/RL Spine. `MERGED` therefore
does not imply `PURIFIED`.

## Bounded publication packet

Start from one theorem-sized target. Do not load the entire repository into an agent context.

The packet contains:

- source title/version/anchor and exact statement;
- target Lean declaration/module;
- assumptions and normalization;
- local/upstream candidates;
- route/frontier parents and expected consumers;
- current reader binding;
- current graph nodes and progress status.

## Author the mathematical meaning once

For each declaration/source obligation, maintain:

### Source contract
- full attributed source statement;
- exact source version and theorem/page/section locator;
- objects, domains, quantifiers, constants, probability mode, feedback model, and regret/sample-complexity convention.

### Reader lesson
- plain mathematical meaning;
- notation;
- hidden/implicit assumptions;
- displayed-formula proof;
- step-to-Lean correspondence;
- exact local dependencies;
- remaining boundary.

### Assumption delta ledger
Classify every material difference as:
- `same`;
- `source-implicit`;
- `mathematically-necessary`;
- `API-limitation`;
- `generalization`;
- `unresolved`.

An API convenience is not a mathematical justification for strengthening the theorem.

## Encoder–denoiser semantic round trip

Follow `.agents/skills/bandit-semantic-roundtrip/SKILL.md`.

The minimum accepted source-facing sequence is:

1. source frozen;
2. Lean statement frozen;
3. source-blind decoder reconstructs the theorem from Lean only;
4. independent source reviewer compares seven slots: objects, quantifiers, assumptions, conclusion, normalization/constants, probability/feedback semantics, and boundary;
5. mismatches are resolved or published as visible mismatch;
6. proposed source repair, if any, is separately reviewed.

A green Lean build cannot replace this.

## Graph publication is the same theorem publication

### Lean Graph
Update/rebuild when module ownership, declaration, import, or reviewed dependency changes. Reuse stable node IDs; do not duplicate shared declarations to make routes look complete.

### Overview / route-progress
Update affected source route, BanditRLwiki setting/case/frontier, result milestone, or roadmap boundary. A dependency theorem does not automatically complete its consumer.

### Functor Hypergraph
Run the conceptual-mirror audit. Routine local lemmas can return `none-found-with-reason`. A recurring mechanism across domains/settings is recorded in `website/content/functor_hypergraph.json` with a failure boundary and candidate formal substrates. It stays conceptual/dashed unless independently formalized.

## Reader rendering rules

The source statement, explanation, proof formulas, hidden assumptions, and folded Lean should be read together. Do not publish a theorem-facing page that is only:

- a declaration count;
- a code dump;
- a giant proof appendix;
- a status badge;
- an unreferenced formula;
- a graph node with no reader explanation.

## Progress truth

Canonical status lives in machine-readable inputs. Never hand-edit generated HTML or chapter completion labels.

A contribution manifest must explicitly classify each affected surface as changed or no-change-with-reason. This prevents "Lean updated, website stale" and the opposite error "website says complete, theorem not compiled".

## Final acceptance

Before requesting merge:

```bash
python3 tools/check_contributor_contract.py --base BASE_COMMIT
python3 tools/bandit.py check
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
git diff --check
```

For a source-facing theorem, the contribution contract must record completed blind decoding and independent source review. For a conceptual bridge, record its evidence status and reviewer.

The PR contains one short integration delta, not a second full proof report.
