# Chapter 17 connected blockers

## Stochastic branch

The former history-law blocker is closed. Theorem 17.1 now composes the
canonical same-randomized-policy history KL identity, original-law expected
pull counts, Gaussian arm KL, Bretagnolle--Huber, the least-pulled alternative,
and the exact source gap. Corollary 17.2 compiles through its Eq. (17.6)
expectation contradiction and exact square-root constants.

Corollary 17.3's exact analytic inequality
`integral_0^infinity exp(-x^(1/p)) dx <= 1` now compiles through a power
substitution and Gamma convexity on `[1,2]`. The terminal remains blocked on
the layer-cake tail rescaling and explicit existence of source-calibrated
`delta,n`. The single-policy/all-horizon/all-confidence quantifiers and real
`p in (0,1)` have not been weakened.

## Adversarial branch

The textbook intentionally gives only a high-level proof of Theorem 17.4. The
remaining formal technology is the same-policy interaction law driven by the
bounded reward matrix, Claim 17.6's information calculation, and Claim 17.7's
clipping concentration. The shared centered-Gaussian product law, exact
`+Delta`/`+2Delta` clipping construction, max-over-fixed-arms random regret,
and construction-level Eq. (17.8) now compile.

Claim 17.5's first-moment witness, the event subtraction, Eq. (17.8), and the
final quarter-horizon algebra compile. They do not discharge Claims
17.6--17.7 or the deterministic-witness assembly.

## Evidence classification

- compiled: Theorem 17.1, Corollary 17.2, threshold definitions, Claim 17.5,
  the shared-noise clipped path, construction-level Eq. (17.8), event
  subtraction, and quarter algebra;
- blocked: Corollary 17.3, Theorem 17.4, and Claims 17.6--17.7;
- route evidence only: Gerchinovitz--Lattimore (2016) and
  `WEAPON-KL-CHANGE-OF-MEASURE`.
