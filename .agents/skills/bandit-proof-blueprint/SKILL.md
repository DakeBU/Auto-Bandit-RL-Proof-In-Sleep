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
- assumption mapping in `conversion-windows/`;
- active proof leaves in `proof-obligations/`;
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
- reviewer checks target fidelity before broad lower proof work.

Stage 2 proof-DAG discharge:

- lower agents prove one active leaf at a time;
- if a leaf is stale or under-specified, middle updates memory first;
- the Lean gate plus synchronized proof map is the only completion gate.

## Reviewer Checklist

- Does the active leaf match the current Lean statement?
- Are all model assumptions explicit?
- Are concentration, measurability, or stopping-time dependencies recorded?
- Is any theorem card being treated as a local proof?
- Did the lower agent update memory after failure?
