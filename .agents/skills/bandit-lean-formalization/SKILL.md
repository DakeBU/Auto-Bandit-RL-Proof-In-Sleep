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
6. If a proof needs Mathlib or LML, stop and record the dependency route
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
