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
- Do not turn proof weapons into proof steps.  They may explain route
  selection, but the exported proof must point to compiled Lean declarations,
  imported theorem cards, or explicit cited-result status.
- Record unproved concentration, measurability, or stopping-time facts as
  obligations.
- Keep the theorem statement no stronger than the compiled Lean statement.
- Update `proof-obligations/` if the export reveals a missing lemma.
- For paper-proof completion tasks, keep the conversion window synchronized
  line by line: paper notation, Lean statement, leaf declarations, compiled
  theorem, then Markdown/LaTeX paragraph.

## Typical Sections

1. Model and notation.
2. Algorithm definition.
3. Reusable lemmas.
4. Regret decomposition.
5. Concentration or posterior argument.
6. Final bound.
7. Lean declaration list.

## Current Chapter 16 export

The synchronized Chapter 16 export is under
`paper-notes/problem-exports/TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE/`.
It records the compiled finite-mean source producer and exact Theorems 16.2,
16.4 and Lemma 16.3. Theorem 16.2 uses exact n-pull horizons, extended-real
inverse-infimum aggregation, and finite-count Fatou. Its consistency premise
is not replaced by assumed intermediate liminf conclusions.

Use the paper title exactly as follows when regenerating this export:

```text
ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory
```
