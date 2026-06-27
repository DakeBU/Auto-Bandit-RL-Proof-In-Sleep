# Lean Style

ABRL starts with a dependency-light Lean core and grows toward Mathlib/LML only
when a task needs that strength.

## Current Layer

- Use `Std` and Lean core for finite executable structures.
- Keep theorem-card records and automation contracts build-tested.
- Avoid `sorry`, `admit`, `axiom`, and `postulate`.
- Prefer small named declarations over long tactic blocks.
- Do not introduce an assumption only to make a theorem easy.
- Decompose aggressively: one lower-agent leaf should fit in one context
  window.
- Specify the local API and intended proof route before tactic search.
- Do not frequently change proof strategy.  Repair the current route unless a
  reviewer records a reason to pivot.

## Mathlib-Ready Leaves

The default target for general leaf lemmas is Mathlib.  A lemma that is about
measurability, integrability, finite sums, boundedness, continuity,
nonemptiness, concentration infrastructure, or generic order/algebra should be
written in a style that can plausibly upstream to
https://mathlib-initiative.org/.

Classify each leaf as:

- `mathlib-candidate`: general enough for Mathlib;
- `project-local`: ABRL-specific wrapper or domain statement;
- `theorem-card-only`: known upstream result not yet local.

For `mathlib-candidate` leaves, keep assumptions explicit and reusable.  Avoid
bandit-specific names unless the theorem is genuinely about bandits.
Each new general leaf should either match an entry in
`research-wiki/theory-tree/mathlib-foundation-leaf-map.md` or add a new entry
there before proof work starts.  The row label is not enough: the task packet
must still give the exact Lean-facing statement, local APIs/imports, intended
route, regularity contracts, and failure policy.

Before creating such a leaf, search the retrieval memory:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-mathlib
python3 tools/bandit.py search-memory QUERY
python3 tools/bandit.py list-lean-decls QUERY
```

Record the Mathlib card id, candidate imports, and search terms tried in the
conversion window or proof-obligation ledger.

Before opening a new finite-bookkeeping leaf, also search local compiled
leaves:

```bash
python3 tools/bandit.py search-memory pullCount
python3 tools/bandit.py search-memory pseudoRegret
python3 tools/bandit.py list-lean-decls pullCount
```

The current local bridge module is `BanditRLProof.LeafLemmas`.

## Mathlib/LML Layer

When a task needs probability, kernels, conditional distribution, integrals,
asymptotics, or concentration:

1. create a conversion window;
2. list the needed Mathlib or LML declarations;
3. decide whether to port or import;
4. isolate toolchain and dependency changes;
5. run `lake build && lake build Tests`;
6. update attribution and memory.

## Reviewer Checks

Run:

```bash
python3 tools/bandit.py check
```

Then inspect:

- whether the theorem statement still matches the task;
- whether persistent failure has triggered a statement/hypothesis audit;
- whether hidden regularity has been promoted to reusable contracts;
- whether Mathlib-candidate leaves are small and general enough;
- whether theorem-card names are marked as local proofs only after import/port;
- whether failed proof fragments were stored in `proof-attempts/`;
- whether proof-export prose names exactly the compiled declarations.
