# Sleep Run Guide

The sleep-run loop creates repeated hierarchical prompt decks and optional
agent executions.

## Dry Run

```bash
python3 tools/bandit.py sleep-run TASK_ID --cycles 2 --lower-count 3
```

This creates run directories and prompt files but does not call an external
agent.

## Executed Run

```bash
python3 tools/bandit.py sleep-run TASK_ID \
  --cycles 2 \
  --lower-count 3 \
  --execute \
  --agent-cmd 'codex exec --cd {root} < {prompt}' \
  --check-each-cycle \
  --stop-on-error
```

Placeholders:

| Placeholder | Meaning |
| --- | --- |
| `{root}` | repository root |
| `{prompt}` | prompt file |
| `{run}` | run directory |
| `{task}` | task id |
| `{cycle}` | cycle number |

You can also use a JSON profile:

```bash
python3 tools/bandit.py sleep-run TASK_ID \
  --cycles 2 \
  --execute \
  --agent-profile codex-parallel.example.json \
  --check-each-cycle
```

## Closeout

After a run:

```bash
python3 tools/bandit.py trial-summary
python3 tools/bandit.py memory-refresh TASK_ID --run-id latest
python3 tools/bandit.py blueprint-refresh TASK_ID
python3 tools/bandit.py check
```
