# Default Hierarchical Run

Use this for first-pass theorem-card to Lean mapping.

```bash
python3 tools/bandit.py sleep-run TASK_ID \
  --cycles 2 \
  --lower-count 3 \
  --check-each-cycle
```

External-agent execution:

```bash
python3 tools/bandit.py sleep-run TASK_ID \
  --cycles 2 \
  --lower-count 3 \
  --execute \
  --agent-cmd 'codex exec --cd {root} < {prompt}' \
  --check-each-cycle \
  --stop-on-error
```
