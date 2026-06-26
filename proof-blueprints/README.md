# Proof Blueprints

Generated snapshots from:

```bash
python3 tools/bandit.py blueprint-refresh TASK_ID
```

Blueprints should expose the same Mathlib-ready leaf fields as the live task:
local APIs/imports, intended proof route, regularity contracts, Mathlib status,
and persistent-failure signal.
