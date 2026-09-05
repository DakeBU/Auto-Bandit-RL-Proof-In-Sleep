# Chapter 14 common-density formula route

Source: `TXT-LATTIMORE-SZEPESVARI-2020`, Eq. (14.6).
For probability measures `P,Q` dominated by a common sigma-finite `mu`, put
`p=dP/dmu` and `q=dQ/dmu`. The supported integrable branch is the `mu` integral
of `p log(p/q)`; singular or nonintegrable branches must remain infinite.

Retrieval: `commonDensityKL` has no local memory/declaration match.
The installed Mathlib provides `Measure.rnDeriv_eq_div`,
`lintegral_rnDeriv_mul`, `integrable_toReal_rnDeriv_mul_iff`, and
`integral_toReal_rnDeriv_mul` in the RN decomposition module. Existing project
probability KL adapters provide the exact finite integral branch.
Cards: `MLIB-MEASURE-INTEGRAL` and the KL/RN source APIs; no new dependency.

Route before tactics: under `P << Q`, transfer the Q-a.e. RN ratio identity
to P-a.e. and take logarithms. Transport integrability and the integral along
the P-density to `mu`. Expose an exhaustive if/else formula retaining both
failure branches. Separately transport the nonnegative `klFun` lower integral
along the Q-density; this handles nonintegrable KL without a real-integral
convention. Generic bridges are Mathlib-candidates. The common dominating
measure is sigma-finite, not assumed finite, and zero density is not excluded.

This is a new focused leaf; the ongoing full gate for commit `40c56ca` does
not cover it. Do not report it as integrated until separately validated.

## Focused proof result

All five declarations in `CommonDensityKL.lean` pass direct Lean checking
and its focused build succeeds (2,671 jobs). The focused canary also passes,
including an arbitrary sigma-finite dominating measure and Lebesgue measure
on the real line. Printed dependencies are only `propext`, `Classical.choice`
(displayed as `choice` because that namespace is open), and `Quot.sound`.

The declarations expose the P-a.e. log-density identity, weighted-integrand
integrability equivalence, supported Eq. (14.6), an exhaustive probability-law
if/else formula, and the nonnegative convex-integrand formula for finite laws.
The only initial compiler error was missing classical decidability for the
if-condition in the theorem statement; a local `open Classical in` resolved
it. No mathematical assumption changed. Root/aggregate integration and
the corresponding full harness/site gates remain pending for this leaf.

The module and its canary have now been added to the root library and aggregate
Tests target; the canary now imports `BanditRLProof`. This prepares a new
integration snapshot but is not itself proof that those aggregate gates pass.

## Integration gate result

At commit `78846b8`, `python tools/bandit.py check` in the short validation
checkout `C:/a14` passed: root library, aggregate Tests (8,903 jobs), proof
graph export, placeholder scan, and 400 Python tests (7 skipped, 185.055s).
Log: `C:/a14/tmp/ch14-common-density-full-check.log`. This closes the Lean
integration gate for Eq. (14.6), not the remaining Chapter 14 body claims.
Website rebuild/publication and detailed export synchronization remain separate.
