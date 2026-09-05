# Chapter 15 integration review

The required body is §15.1 Lemma 15.1 and §15.2 Theorem 15.2, including
their proof dependencies and exact Gaussian constant 1/27. It is compiled.
Optional Notes and Exercises are assessed separately: Exercise 15.7 remains
partial, with stopped-history information and F_tau factorization open.

## Integration with main 102c5cd

Ch13 and Ch14 acceptance records are retained. Generated indexes and trial
summaries are regenerated after combining the append-only evidence records.

Ch14 now supplies `relativeEntropy_trim_le` for arbitrary sub-sigma-algebras
and `relativeEntropy_map_eq_trim_of_absolutelyContinuous` for measurable maps.
The Ch15 public theorem `klDiv_map_le` keeps its exact finite-measure statement
and now wraps those APIs. Infinite source KL is discharged by `le_top`; finite
KL supplies absolute continuity for the map/trim identity. This removes the
duplicate conditional-Jensen proof and its increased heartbeat limit.

The fixed-history wrapper still counts all pulls through `lastRound`.
There is no change to Lemma 15.1, Theorem 15.2, their policy class, KL direction,
first-law expectations, Gaussian variance, unit-cube means or constant.

This is a direct integration review. The checked public declarations and
source contract support required-body completion; they do not close the
optional stopping-time exercise. Current-commit CI and publication evidence
will be linked in PR #102 after verification.
