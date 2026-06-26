---
name: bandit-mathlib-retrieval
description: Retrieve Mathlib APIs and reusable lemma routes before creating ABRL Mathlib-candidate proof leaves.
argument-hint: "[query term or task id]"
---

# Bandit Mathlib Retrieval

Use this skill before proving any general-purpose lemma about finite sums,
order/algebra, measurability, integrability, probability, kernels,
asymptotics, convexity, or linear algebra.

## Required Commands

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-mathlib
python3 tools/bandit.py list-papers
python3 tools/bandit.py search-memory <query>
python3 tools/bandit.py list-lean-decls <query>
```

## Required Files

Read:

- `research-wiki/mathlib/theorem-cards.md`;
- `research-wiki/mathlib-candidates/README.md`;
- `research-wiki/papers/bandit-frontier-cards.md` when the leaf comes from a paper route;
- the task conversion window;
- the task proof-obligation ledger.

## Retrieval Packet

Before lower Lean work, record:

- Mathlib card id;
- textbook or paper source card id;
- candidate imports/modules;
- search terms already tried;
- compiled local declarations already found;
- expected local API bridge;
- intended proof route;
- hidden regularity contracts;
- status: `import-candidate`, `port-candidate`, `mathlib-candidate`,
  `project-local`, or `not-found`.

## Reviewer Rule

Reject a new generic ABRL lemma if the attempt did not first check the Mathlib
retrieval cards.  Repeated search failure is mathematical signal: the theorem
may need a missing assumption, a different abstraction, a different existing
name, or a genuine upstream contribution.
