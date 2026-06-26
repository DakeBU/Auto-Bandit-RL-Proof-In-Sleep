# Tasks

Task packets are the user-facing contracts for ABRL runs.  A task must state
the theorem target, source, Lean file, proof obligations, and acceptance gate.

Every task that opens proof-DAG leaves must also maintain the Mathlib-ready leaf
contract in its conversion window and proof-obligation ledger: local APIs,
intended proof route, hidden regularity contracts, Mathlib status, and failure
signal.  General leaves should be prepared as future Mathlib contributions
whenever possible.

Every theorem task should name a textbook/source card, a scenario card, and
the Mathlib/LML retrieval cards expected for the first active leaves.

Create new tasks with:

```bash
python3 tools/bandit.py new-task TASK_ID --title "..." --target-lean BanditRLProof/...
```
