# Mathlib Upstream Policy

ABRL's proof leaves should be designed as future Mathlib contributions whenever
they are general enough.  The target is not only to make ABRL pass locally, but
to leave reusable Lean mathematics for the wider Lean community.

The operational diagrams for this policy are in
[`docs/lemma_leaf_network.md`](lemma_leaf_network.md).

## Leaf Standard

Every active proof-DAG leaf should be:

- small enough for one agent context window;
- named as a reusable lemma, not hidden inside a long theorem proof;
- stated over general structures when that does not distort the theorem;
- accompanied by local API pointers and intended proof route;
- free of ABRL-specific terminology unless it is truly domain-specific;
- compatible with Mathlib naming, namespace, and hypothesis style where
  possible.

## Before Tactic Work

Middle or upper must record:

1. exact statement;
2. expected imports;
3. local APIs and existing lemmas;
4. intended proof route;
5. required regularity hypotheses;
6. whether the lemma is `mathlib-candidate`, `project-local`, or
   `theorem-card-only`.

Lower agents should not start broad tactic search before these are written.

## Persistent Failure Rule

Repeated failure is evidence.  After repeated attempts on the same leaf,
stop and classify the blocker before changing the proof:

- statement is false or too strong;
- missing hypothesis;
- missing regularity condition;
- wrong abstraction;
- API mismatch;
- theorem already exists under another name;
- proof route is unstable.

Only pivot after recording that diagnosis in `proof-attempts/` or
`proof-obligations/`.

## Hidden Regularity Contracts

Do not bury regularity requirements in local proof scripts.  The following
should become reusable theorem contracts:

- integrability;
- measurability;
- continuity;
- nonemptiness;
- boundedness;
- finite support or finite action set;
- positivity/nonzero denominators;
- summability;
- adaptedness or stopping-time conditions.

If the contract belongs in Mathlib, mark it `mathlib-candidate`.

Store proposed upstream leaves in `research-wiki/mathlib-candidates/` with the
statement, required imports, local APIs, intended proof route, and current
failure signal.

Before adding a candidate, search `research-wiki/mathlib/theorem-cards.md` and
the compact JSON index:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py search-memory QUERY
```

A candidate record should say whether the needed result was found under a
different Mathlib name, requires a new bridge lemma, or appears to be a genuine
upstream gap.

## Proof Stability Rule

Agents should not frequently change proof strategy.  The default is to repair
the current proof route, preserving useful intermediate lemmas.  A route
change needs a recorded reason from middle or reviewer.
