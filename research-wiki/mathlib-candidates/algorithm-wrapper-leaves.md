# Algorithm Wrapper Leaves

Status: local compiled project wrappers.

These leaves are intentionally ABRL-specific.  They are not direct Mathlib
upstream candidates, but they identify the generic finite-index and order APIs
that algorithm proofs should bridge to.

## Compiled Local Wrappers

| Local declaration | Role | Retrieval cards | Future action |
| --- | --- | --- | --- |
| `ETC.exploreArm_eq_of_mod_eq` | round-robin exploration is determined by the time modulo arm count | `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | bridge ETC count proofs to generic modular arithmetic and finite index lemmas |
| `UCB.score_eq_empiricalMean` | current dependency-light UCB score unfolds to empirical mean | `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT` | replace with log/sqrt confidence-width theorem when Mathlib layer is selected |

## Reviewer Rule

Algorithm wrappers can stay project-local.  General arithmetic, finite-index,
or order facts used inside them should be routed through Mathlib retrieval
cards or recorded as `mathlib-candidate` leaves.
