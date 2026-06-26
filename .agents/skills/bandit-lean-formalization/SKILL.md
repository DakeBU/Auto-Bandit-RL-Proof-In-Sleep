---
name: bandit-lean-formalization
description: Formalize ABRL bandit/RL definitions and proof leaves in Lean while preserving theorem targets and harness memory.
argument-hint: "[Lean file or task id]"
---

# Bandit Lean Formalization

Use this skill when editing `BanditRLProof/` or `Tests/`.

## Rules

1. Run `python3 tools/bandit.py check` before claiming completion.
2. Do not use `sorry`, `admit`, `axiom`, or `postulate`.
3. Keep theorem statements aligned with the conversion window.
4. Prefer small definitions and lemmas with stable names.
5. Do not add assumptions unless middle recorded them in the task ledger.
6. Before tactic work, record local APIs/imports and the intended proof route.
7. Do not frequently change proof strategy; repair the current route unless
   reviewer or middle records a mathematical reason to pivot.
8. If repeated attempts fail, treat that as signal to audit the statement,
   missing assumptions, or counterexamples.
9. Before creating a general-purpose lemma, run `python3 tools/bandit.py
   search-memory <term>`, run `python3 tools/bandit.py list-lean-decls <term>`,
   use `python3 tools/bandit.py list-lean-decls <term> --statement` when the
   exact local statement matters, and check
   `research-wiki/mathlib/theorem-cards.md`.
10. If a general leaf belongs in Mathlib, mark it `mathlib-candidate` and keep
   ABRL-specific wrappers thin.
11. If a leaf comes from a paper theorem, record the paper card id before
   tactic work.
12. If a proof needs Mathlib or LML, stop and record the dependency route
   before changing `lakefile.lean`.

## Current Lean Layer

The initial ABRL layer is dependency-light.  It supports:

- finite action traces;
- pull counts;
- reward sums;
- rational finite-arm mean models;
- pseudo-regret surfaces;
- theorem-card records and automation contracts.

Probability, kernels, expectations, and concentration are currently theorem
cards or obligations unless a task explicitly adds the dependency layer.

## Failure Output

For a failed proof, write:

- exact target;
- remaining goal or compiler error;
- useful local lemmas;
- whether the failure is source mapping, theorem-card dependency, Lean API, or
  invalid target.
- missing regularity contract or possible counterexample;
- Mathlib candidacy and the current proof route stability note.
