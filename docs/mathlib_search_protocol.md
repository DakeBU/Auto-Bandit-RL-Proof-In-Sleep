# Mathlib Search Protocol

ABRL should reuse Mathlib before creating a new general lemma.  The goal is to
make Mathlib-usable leaves easy to find, import, port, or upstream.

## Fast Path

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-mathlib
python3 tools/bandit.py list-papers
python3 tools/bandit.py list-weapons
python3 tools/bandit.py search-memory Finset.sum
python3 tools/bandit.py search-memory integrable
python3 tools/bandit.py search-memory contextual
python3 tools/bandit.py list-lean-decls pullCount
python3 tools/bandit.py list-lean-decls between --statement
```

Then read:

- `research-wiki/mathlib/theorem-cards.md`;
- `research-wiki/mathlib-candidates/README.md`;
- the task conversion window;
- the task proof-obligation ledger.

## Search Order

1. Search ABRL memory with `search-memory`.
2. Confirm the textbook or paper source card for the scenario.
3. If a technique name appears, search `list-weapons`, then decompose the
   weapon into concrete theorem cards and leaves.
4. Search the local Lean declaration index with `list-lean-decls`.
5. Search the Mathlib docs with the card's module and query terms.
6. Search local Lean code and existing theorem cards.
7. If the result exists upstream, record the import route.
8. If it is general but missing, record a `mathlib-candidate`.
9. If it is ABRL-specific, keep the wrapper project-local and thin.

## Required Leaf Fields

Every Mathlib-related leaf must record:

- source card id;
- exact intended import;
- candidate declaration names or search terms;
- local API bridge;
- intended proof route;
- regularity contracts;
- import/port/upstream decision;
- failure signal if the route stalls.

## Rejection Rule

Do not add a new generic lemma to ABRL just because a lower agent did not find
the Mathlib API quickly.  Repeated search failure should be recorded as
mathematical signal: missing assumption, wrong abstraction, theorem under a
different name, or genuine upstream gap.
