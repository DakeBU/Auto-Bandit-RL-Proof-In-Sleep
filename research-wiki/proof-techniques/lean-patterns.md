# Lean Patterns For ABRL

## Dependency-Light Layer

Use recursive definitions when possible:

- `pullCount action arm 0 = 0`;
- `pullCount action arm (t + 1)` unfolds by `rfl`;
- `sumRewards` follows the same pattern.

This avoids needing Mathlib finite sums for early executable tests.

## Theorem-Card Layer

When a theorem needs probability or measure theory, record the upstream
declaration first.  Do not recreate a large API from memory.

Good theorem-card fields:

- declaration;
- module;
- assumptions;
- proof role;
- local status;
- import or port plan.

## Mathlib/LML Layer

Before adding dependencies:

1. write the exact target in `conversion-windows/`;
2. list the required imports;
3. decide whether toolchain alignment is acceptable;
4. run the full gate;
5. update attribution.

## Mathlib-Ready Leaf Nodes

A leaf lemma should be small enough for one lower-agent context window.  Before
tactic work, record:

- exact statement;
- required imports and local APIs;
- intended proof route;
- hidden regularity contracts;
- Mathlib status: `mathlib-candidate`, `project-local`, or `theorem-card-only`.

When a proof repeatedly fails, treat that as evidence.  Recheck the theorem
statement, missing assumptions, API availability, and counterexamples before
changing the proof route.  Agents should repair the current route by default;
frequent proof-strategy churn must be recorded as a reviewer-visible pivot.

## Common Failure Classes

- `source translation gap`: prose theorem is not mapped to Lean symbols.
- `theorem-card dependency`: upstream theorem is known but not local.
- `semantic interface gap`: local ABRL definitions cannot express the theorem.
- `local Lean lemma gap`: proof needs a small compiled lemma.
- `missing regularity contract`: integrability, measurability, continuity,
  nonemptiness, boundedness, positivity, summability, or adaptedness is not
  available as a reusable theorem contract.
- `likely false statement or counterexample`: persistent failure indicates the
  statement may be too strong.
- `invalid route`: proof changed assumptions or target.
