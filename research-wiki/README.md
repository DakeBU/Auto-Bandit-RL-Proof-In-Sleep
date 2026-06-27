# Research Wiki

This wiki stores reusable theorem cards, proof techniques, cited results, and
open proof technology for ABRL agents.

The rule is simple: if a fact is useful for future proof work, store it here
instead of leaving it only in a run transcript.

## Memory Areas

- `lml/`: theorem cards from LeanMachineLearning/LML.
- `mathlib/`: Mathlib retrieval cards for reusable Lean leaf lemmas.
- `textbooks/`: classic textbook and survey source cards.
- `scenarios/`: current bandit/RL scenario taxonomy.
- `theory-tree/`: broad proof tree and fine-grained Mathlib foundation leaf map.
- `cited-results/`: external theorem contracts not yet local.
- `proof-weapons/`: upper-layer route inspiration that must be decomposed into
  concrete theorem cards and leaves.
- `proof-techniques/`: reusable Lean and mathematical proof routes.
- `mathlib-candidates/`: general leaf lemmas to prepare for upstream Mathlib
  contribution.
- `open-problems/`: unresolved proof technology and blocked routes.
- `retrieval-index/`: compact JSON prompt memory.

Two top-level docs should be read before broad theorem work:

- `docs/completion_gap_audit.md`: what is compiled now versus still carded or
  missing.
- `docs/adaptive_harness_design.md`: how upper route population, middle memory
  maintenance, Lean workers, retrieval workers, and natural-language prover
  branches coordinate.
