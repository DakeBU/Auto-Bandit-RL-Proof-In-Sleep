# Proof Export

ABRL exports compiled proofs into Markdown and LaTeX so that a human reader can
use the result outside Lean.

## Command

```bash
python3 tools/bandit.py export-proof TASK_ID --title "Theorem title"
```

This writes:

```text
paper-notes/problem-exports/<task-id>/latest.tex
paper-notes/problem-exports/<task-id>/latest.md
```

## Export Rules

- Name every Lean declaration used.
- State definitions before theorem statements.
- Do not claim a theorem is proved if it is only a theorem card.
- Record unproved concentration, measurability, or stopping-time facts as
  obligations.
- Keep the theorem statement no stronger than the compiled Lean statement.
- Update `proof-obligations/` if the export reveals a missing lemma.

## Typical Sections

1. Model and notation.
2. Algorithm definition.
3. Reusable lemmas.
4. Regret decomposition.
5. Concentration or posterior argument.
6. Final bound.
7. Lean declaration list.
