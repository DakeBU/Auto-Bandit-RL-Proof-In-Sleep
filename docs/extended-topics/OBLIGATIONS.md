# Obligation graph (mathematical workflow, not elaborated dependencies)

```mermaid
flowchart TD
  M[Raw moment and measurable independent coordinates] --> B[Truncation bias: compiled]
  M --> V[Truncated second moment: compiled]
  V --> G[Centered fixed-tilt MGF: compiled]
  E[Existing EXP3 exponential remainder] --> G
  G --> T[Independent fixed-prefix one-sided tail: compiled]
  B --> U[Two-sided mean confidence with explicit sums: compiled]
  T --> U
  H[Existing next-unused-coordinate prefix proof] --> P[Transformed actual prefix: compiled]
  P --> H2[Causal observed-history policy: compiled]
  H2 --> A[Adaptive-count tail: compiled]
  U --> S[Sample-index power-radius tuning: compiled]
  S --> A
  A --> R[Conservative expected robust-UCB regret: compiled candidate]
  P --> C[Actual clipped-corruption stability: compiled]
  L[Clipping is 1-Lipschitz] --> C
  C --> Q[Clean clipped confidence plus corruption: OPEN]
```

Exact compiled type/value references are emitted separately by
`tools/extended_topics_evidence.py`. This diagram does not assert that a source
arrow is a Lean proof-term dependency. It also does not infer completion of the
endpoint from compiled predecessor leaves.

The shared `.lake/packages` junction points to canonical pinned dependencies;
the worktree has its own `.lake/build`. This development setup is allowed for
proof work but is explicitly unsuitable for a Mathlib-only isolation experiment.
