# Local Dual-Agent Review Prompt: After Oracle Wrong-Event Coordinate Measurability

We are working in the Lean 4 project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` is compiled
  locally.
- `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` remains theorem-card-only, not a
  local proof.
- The historical Extended Pro path is no longer required for current work.
  When route judgment is needed, run two local agents, compare their advice,
  and record a combined local review artifact before editing Lean.

Candidate A:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Do not implement a concrete argmax oracle yet. Write the exact route card for
constructing a finite argmax-backed `ETC.CommitOracle K` later, including
tie-breaking, `Fin K` nonemptiness, selected score maximality, measurability
contracts, and how it will feed the existing abstract oracle argmax consumer.

Candidate B:

`ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`

Do not prove concentration. Write the exact import-route card for the future
pairwise empirical-mean tail assumption consumed by the compiled probability
wrappers, including measurable events, probability measure assumptions,
independence or filtration/adaptedness, bounded/sub-Gaussian reward contracts,
integrability, and the exact local tail-consumer target.

Candidate C:

`FILTRATION-HISTORY-ROUTE-CARD`

Do not implement filtration yet. Write the exact route card for finite history
sigma-algebras and filtration/adaptedness contracts that would later support
conditionally sub-Gaussian rewards and martingale differences.

For the selected leaf/card, provide:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or
  theorem-card-only;
- failure policy.

Also state explicitly which candidates should not be attempted in the same
batch.
