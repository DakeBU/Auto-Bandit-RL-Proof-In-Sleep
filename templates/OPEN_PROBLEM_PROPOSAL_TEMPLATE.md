# Open Problem Proposal

Problem id: `BRL-OP-XXX`

## Title

## Motivation

Which theorem, paper, or failed Lean proof exposes this gap?

## Formal Target

State the Lean declaration or interface that would close the gap.

## Source And Theorem Cards

- Paper/repository:
- Upstream Lean declaration:
- Cited result:

## Acceptance Test

```bash
lake build && lake build Tests
```

## Memory Update

```bash
python3 tools/bandit.py trial-log --task TASK_ID --role reviewer --kind proposal --status queued --notes "..."
python3 tools/bandit.py memory-refresh TASK_ID
```
