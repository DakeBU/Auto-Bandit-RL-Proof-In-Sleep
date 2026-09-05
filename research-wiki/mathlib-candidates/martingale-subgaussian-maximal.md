# Martingale subgaussian finite maximal bound

Task: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`.
Source: Theorem 9.2 supporting Algorithm 7 / Chapter 13's broader-class claim.
Cards: `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-PROBABILITY-SUBGAUSSIAN`,
`MLIB-MEASURE-INTEGRAL`; textbook `TXT-LATTIMORE-SZEPESVARI-2020`.

Status: mathlib-candidate, locally compiled; dedicated full-statement canary
passes (3473-job build), with baseline axioms only. New full integration
pending. This is not an upstreamed Mathlib result.

## Frozen route

For a real martingale S on a probability measure with filtration F and
integrable exponentials at every time, conditional Jensen proves exp(t*S)
is a nonnegative submartingale. Doob's finite maximal inequality bounds
`P(exists i<=n, epsilon<=S_i)` by exp(-t*epsilon+c*t^2/2) for t>0 when the
terminal S_n has subgaussian proxy c. Optimization at t=epsilon/c gives
exp(-epsilon^2/(2c)) for epsilon,c>0. This is one-sided, finite-time uniform,
without a cardinality factor. The source partial-sum producer from independent
centered subgaussian increments remains a distinct downstream obligation.

Imports: `Martingale.OptionalStopping`, conditional-expectation `CondJensen`,
`Moments.SubGaussian`, exponential convexity. Existing APIs:
`Martingale.smul`, `ConvexOn.map_condExp_le_univ`,
`MeasureTheory.maximal_ineq`, `HasSubgaussianMGF.integrable_exp_mul`,
`HasSubgaussianMGF.mgf_le`, finite sup and restricted-integral monotonicity.
Searches: `search-memory maximal_ineq`, `list-lean-decls maximal_ineq
--statement`, pinned Mathlib martingale/conditional-Jensen sources.

Regularity: probability measure, strongly adapted real martingale, explicit
exponential integrability for all time indices, positive tilt/threshold,
positive terminal variance proxy for optimized division. No independence is
added at this generic level; it must be proved for the source partial sums.
The planned producer must identify zero mean and the actual natural filtration.

## Independent source producer route

The generic exponential-submartingale and optimized maximal bounds now pass
Lean. The independent centered coordinate producer also passes Lean, using
the existing
`MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference`,
`Filtration.stronglyAdapted_natural`, and
`iIndepFun.condExp_natural_ae_eq_of_lt` (Mathlib `Probability.BorelCantelli`).
Use explicit zero coordinate integrals (supplied by centering rewards at
their actual means), coordinate strong measurability and subgaussian MGFs.
`HasSubgaussianMGF.sum_of_iIndepFun` after injective successor reindexing
gives proxy n*c and all exponential integrability. The sums use X1 through
Xn; X0 is an unused independent coordinate of the natural filtration.
This does not relax MOSS's target: its centered arm-stream model must later
produce these coordinate hypotheses from the actual reward laws.
