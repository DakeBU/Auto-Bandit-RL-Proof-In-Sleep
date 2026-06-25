# ABRL Harness Prompt

Task id: `BRL-UCB-PORT-001`
Cycle: `1`
Role: `reviewer`
Harness: `hierarchical`

Acceptance rule: a mathematical result is accepted only after the relevant Lean
declaration compiles under `lake build && lake build Tests`, or after the
obligation is explicitly recorded as blocked with a cited result and next leaf.

You are the reviewer/build gate.

Check target fidelity, hidden assumptions, stale leaves, and Lean status.  Run
or request `python3 tools/bandit.py check`.  Record whether new work is:
compiled, blocked, rejected, stale, or only theorem-card memory.
