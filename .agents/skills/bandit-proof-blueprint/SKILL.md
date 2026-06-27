---
name: bandit-proof-blueprint
description: Refresh and use ABRL proof-blueprint snapshots as the system-of-record layer for long bandit/RL Lean proof runs.
argument-hint: "[task id]"
---

# Bandit Proof Blueprint

Use this skill before long formalization or proof-repair runs.

ABRL adapts the blueprint and dynamic-leaf discipline studied in
LeanMarathon to bandit/RL proof work.  The blueprint is a compact snapshot
over:

- task target in `tasks/`;
- Lean declarations in `BanditRLProof/`;
- theorem cards in `research-wiki/lml/`;
- Mathlib cards in `research-wiki/mathlib/`;
- textbook and scenario cards in `research-wiki/textbooks/` and
  `research-wiki/scenarios/`;
- proof weapon cards in `research-wiki/proof-weapons/`, used only as route
  inspiration;
- proof tree memory in `research-wiki/theory-tree/`;
- assumption mapping in `conversion-windows/`;
- active proof leaves in `proof-obligations/`;
- Mathlib candidate leaves in `research-wiki/mathlib-candidates/`;
- recent attempts in `runs/trials.jsonl`.

## Required Command

```bash
python3 tools/bandit.py blueprint-refresh <task-id>
```

## Stage Rules

Stage 1 target stabilization:

- map the theorem statement, assumptions, constants, and source declaration;
- classify LML or paper results as theorem cards, cited results, imports, or
  local compiled declarations;
- attach the target to a textbook card and a scenario card;
- record any proof weapon only as planning context, then decompose it into
  concrete theorem cards and leaves;
- search Mathlib retrieval cards for each reusable leaf before creating a new
  Mathlib candidate;
- reviewer checks target fidelity before broad lower proof work.

Stage 2 proof-DAG discharge:

- lower agents prove one active leaf at a time;
- each active leaf names local APIs, imports, hidden regularity contracts, and
  the intended proof route;
- general leaves are classified as `mathlib-candidate`, `project-local`, or
  `theorem-card-only`;
- if a leaf is stale or under-specified, middle updates memory first;
- persistent failure triggers a statement/hypothesis/counterexample audit
  before broad tactic search continues;
- the Lean gate plus synchronized proof map is the only completion gate.

## Reviewer Checklist

- Does the active leaf match the current Lean statement?
- Are all model assumptions explicit?
- Does the target have a textbook/source card and scenario card?
- Were Mathlib retrieval cards searched before new general lemmas were added?
- Are concentration, measurability, or stopping-time dependencies recorded?
- Are hidden regularity hypotheses promoted to reusable theorem contracts?
- Are general leaf lemmas prepared as Mathlib candidates?
- Is any theorem card being treated as a local proof?
- Is any proof weapon being treated as a theorem card or proof term?
- Did any lower agent change proof route without a recorded reason?
- Did the lower agent update memory after failure?
