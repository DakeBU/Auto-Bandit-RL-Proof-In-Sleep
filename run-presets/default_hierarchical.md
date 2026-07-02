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

Reviewer-gated execution:

```bash
python3 tools/bandit.py sleep-run TASK_ID \
  --cycles 2 \
  --lower-count 3 \
  --require-review-response \
  --check-each-cycle \
  --stop-on-error
```

Use the reviewer-gated form when the current `unfinished` boundary says to wait
for Extended Pro before generating more proof work. It stops before creating a
cycle unless `python3 tools/bandit.py review-status --require-response` passes.
