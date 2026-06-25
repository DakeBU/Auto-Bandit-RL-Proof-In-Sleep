---
name: bandit-open-problem
description: Promote unresolved bandit/RL proof technology into task packets and memory without weakening theorem targets.
argument-hint: "[topic]"
---

# Bandit Open Problem

Use this when a proof route exposes missing formal technology.

## Promotion Criteria

Create or update an open problem when:

- the theorem needs a concentration result not locally available;
- LML has a theorem but toolchain or dependency import is blocked;
- an RL formulation needs a reusable Bellman, occupancy, or regret interface;
- repeated lower attempts fail on the same missing lemma.

## Required Fields

- problem id;
- source theorem or paper;
- formal target;
- current Lean status;
- theorem cards involved;
- acceptance gate;
- next smallest leaf.

## Command Pattern

```bash
python3 tools/bandit.py trial-log \
  --task TASK_ID \
  --role reviewer \
  --kind proposal \
  --status queued \
  --notes "promoted missing concentration lemma into open problem"
```
