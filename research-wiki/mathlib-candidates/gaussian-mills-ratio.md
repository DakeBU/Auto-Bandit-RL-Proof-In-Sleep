# Gaussian Mills-Ratio Tail Bounds

Status: blocked Mathlib-candidate analytic leaf.

Task: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

## Exact source target

For every real `x >= 0`, prove the two inequalities displayed in
Lattimore--Szepesvári Eq. (13.4): the tail integral of `exp (-t^2)` over
`(x, infinity)` is bounded below and above by the printed rational functions
of `x` times `exp (-x^2)`.  Rescaling this leaf must recover both sides of the
Chapter 13 Eq. (13.1) midpoint error bound with exactly the source constants.

## Retrieval audit

- Pinned Mathlib revision: `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
- Searched modules: `Probability.Distributions.Gaussian.Real`,
  `Probability.Moments.SubGaussian`, and
  `Analysis.SpecialFunctions.Gaussian.GaussianIntegral`.
- Available local route: `gaussianPDFReal`, `gaussianReal_apply_eq_integral`,
  `mgf_id_gaussianReal`, `HasSubgaussianMGF.measure_ge_le`, and
  `integral_gaussian_Ioi`.
- Search terms: Gaussian tail, `Ici`/`Ioi`, Mills ratio, Gaussian density,
  and exponential-square tail integral.
- Result: the exact Mills-ratio inequalities were not found.  The compiled
  Chernoff upper bound is weaker and cannot discharge the source display.

## First executable leaf

Prove a generic real-analysis theorem for `x >= 0` bounding
`integral (fun t : Real => Real.exp (-t^2))` over `Set.Ioi x` in both source
directions.  Keep denominator positivity explicit, then derive the standard
normal-tail version and finally the `N(0,1/n)` midpoint specialization.

## Regularity and nonclaims

The integrand's measurability and integrability are available from Mathlib's
Gaussian integral development.  This card is not a theorem and does not make
Eq. (13.1) locally compiled.  Do not substitute the Chernoff inequality for
the missing lower bound or the printed sharpened upper bound.
