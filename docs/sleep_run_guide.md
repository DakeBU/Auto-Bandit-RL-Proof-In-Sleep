# Sleep Run Guide

The sleep-run loop creates repeated evidence-tracked prompt decks and optional
agent executions. Hierarchical remains the default; master–worker is an
experimental matched arm, and adaptive chooses which arm needs evidence next.

## Dry Run

```bash
python3 tools/bandit.py sleep-run TASK_ID --cycles 2 --lower-count 3
```

This creates run directories and prompt files but does not call an external
agent.

## Executed Run

For a route-aware screen packet, print the command plan first:

```bash
python3 tools/bandit.py screen-plan BRL-UCB-PORT-001 \
  --route ROUTE-UCB1-FINITE-STOCHASTIC \
  --cycles 2 \
  --lower-count 4
```

Then run the printed commands in a `screen` session.

```bash
python3 tools/bandit.py sleep-run TASK_ID \
  --cycles 2 \
  --lower-count 3 \
  --execute \
  --agent-cmd 'codex exec --cd {root} < {prompt}' \
  --check-each-cycle \
  --stop-on-error
```

## Matched Harness Experiment

Run both arms from isolated worktrees at the same pinned commit. Freeze the
same target fingerprint and route packet; do not let either arm see the other
arm's output before review.

```bash
python3 tools/bandit.py run-cycle TASK_ID \
  --harness hierarchical --experiment-id AB-001 \
  --target-fingerprint SHA256_OF_FROZEN_TARGET

python3 tools/bandit.py run-cycle TASK_ID \
  --harness master-worker --experiment-id AB-001 \
  --target-fingerprint SHA256_OF_FROZEN_TARGET \
  --lower-count 3 \
  --parallel-route-json run-presets/harness-comparison-routes.example.json

python3 tools/bandit.py harness-compare --task TASK_ID \
  --trials path/to/hierarchical-trials.jsonl \
  --trials path/to/master-worker-trials.jsonl
```

Add `--execute-review --agent-profile codex-parallel.example.json` only when a
GPT interpretation is wanted. Its prose and proposed Mermaid design are
advisory; the deterministic matched-evidence boundary remains authoritative.

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
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
```
