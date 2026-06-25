# Tasks

Task packets are the user-facing contracts for ABRL runs.  A task must state
the theorem target, source, Lean file, proof obligations, and acceptance gate.

Create new tasks with:

```bash
python3 tools/bandit.py new-task TASK_ID --title "..." --target-lean BanditRLProof/...
```
