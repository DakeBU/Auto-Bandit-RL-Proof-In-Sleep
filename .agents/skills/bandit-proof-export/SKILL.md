---
name: bandit-proof-export
description: Translate compiled ABRL Lean proofs into synchronized Markdown and LaTeX without overstating theorem-card status.
argument-hint: "[task id]"
---

# Bandit Proof Export

Use this after Lean closure or during closeout for unresolved tasks.

## Command

```bash
python3 tools/bandit.py export-proof <task-id> --title "Theorem title"
```

## Rules

1. Name every compiled Lean declaration used.
2. Mark theorem cards as upstream references, not local proof certificates.
3. Define notation before theorem statements.
4. Record every unproved concentration or measurability dependency.
5. Keep Markdown and LaTeX synchronized with the conversion window.

## Export Shape

- model and assumptions;
- algorithm definition;
- proof-DAG lemmas;
- regret decomposition;
- concentration or posterior argument;
- final bound;
- exact Lean declaration list.
