# Chapter 15 completion and evidence audit

Date: 2026-09-04

Scope: official Chapter 15 source, current production Lean and typed canary,
task/window/obligation/theorem-card/open-problem/export artifacts, and the
maintained website sources. This is a direct repository audit; independent PR
review remains a remote acceptance gate.

## Source inventory

- §15.1 has one numbered result: Lemma 15.1 / Eq. (15.1).
- §15.2 has one numbered result: Theorem 15.2.
- §15.3 is an informal Notes section whose Fisher/Taylor discussion states
  unspecified smoothness/interchange regularity rather than a numbered result.
- §15.4 is bibliographic context.
- §15.5 contains Exercises 15.1--15.8. Exercise 15.7 states the bounded-
  stopping-time random-element KL inequality and hints at Exercises 14.10 and
  14.9.

Therefore `core_status = compiled` means the exact theorem-bearing body is
closed. `status = partial` means the Notes/Exercises layer is not exhaustive.

## Compiled evidence boundary

- Lemma 15.1: `banditHistoryRelativeEntropy_eq_expectedPulls_sum` retains one
  common randomized policy, the `nu -> nu'` KL direction, and first-law
  expected realized pull counts.
- Theorem 15.2: `finiteArmedGaussianMinimaxLowerBound` retains `k>1`,
  `n>=k-1`, unit variance, unit-cube means, and the exact `1/27` constant;
  `unitGaussianMinimaxExpectedPseudoRegret_ge` is its minimax consequence.
- Exercise 15.7 dependency: `klDiv_map_le` proves generic finite-measure data
  processing under any measurable observation, and
  `klDiv_observedBanditHistory_le_expectedPulls_sum` combines it with the
  deterministic-horizon Lemma 15.1 identity.

## Remaining exact gap

Exercise 15.7 is not compiled. The missing route is a measurable bounded
stopped-history law, a KL bound that charges arm information only through the
realized stop, and factorization of an arbitrary `F_tau`-measurable random
element through that stopped history. The compiled deterministic-horizon
corollary cannot be relabelled as this theorem because its right-hand side
still counts all pulls through a fixed terminal horizon.

## Verification record

The final focused/root/Tests/harness/site/browser results are recorded in the
task packet and PR. Until those gates pass, this audit does not promote remote
or deployment status.
