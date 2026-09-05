# Gaussian Mills-Ratio Tail Bounds

Status: blocked Mathlib-candidate analytic leaf.

Task: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

## Exact source target

For every real `x >= 0`, prove the two inequalities displayed in
Lattimore--Szepesvári Eq. (13.4): the tail integral of `exp (-t^2)` over
`(x, infinity)` is bounded below and above by the printed rational functions
of `x` times `exp (-x^2)`.  Rescaling this leaf must recover both sides of the
Chapter 13 Eq. (13.1) midpoint error bound with exactly the source constants.

The exact frozen formula (physical PDF p. 193) is

```text
exp(-x^2)/(x + sqrt(x^2 + 2))
  <= integral_{x}^{infinity} exp(-t^2) dt
  <= exp(-x^2)/(x + sqrt(x^2 + 4/pi)),  x >= 0.
```

For `q = n*Delta^2`, `n>0`, `Delta>0`, physical PDF p. 190 is

```text
sqrt(8/pi)*exp(-q/8)/(sqrt(q) + sqrt(q+16))
  <= P_0(sampleMean >= Delta/2)
  <= sqrt(8/pi)*exp(-q/8)/(sqrt(q) + sqrt(q+32/pi)).
```

The change of variable is `x = sqrt(n)*Delta/(2*sqrt(2))` and the
probability is `integral_x^infinity exp(-t^2) dt / sqrt(pi)`.

## Analytic route audited 2026-09-05

Write `F_c(x) = exp(-x^2)/(x + sqrt(x^2+c))` for `c>0`.
Differentiation gives
`F_c'(x) = -F_c(x)*(2*x + 1/sqrt(x^2+c))`.
For `c=2`, `-F_c'(x) <= exp(-x^2)` on `x>=0` follows from
`(sqrt(x^2+2)-x)*sqrt(x^2+2) >= 1`.
Integrate this inequality to infinity, using `F_2 -> 0`, to obtain the
exact source lower bound. Pinned Mathlib exposes
`integral_Ioi_of_hasDerivAt_of_nonpos'` and
`integrableOn_Ioi_deriv_of_nonpos'` in
`Mathlib.MeasureTheory.Integral.IntegralEqImproper`; these provide the
improper-integral step without an assumed derivative-integrability premise.

The upper constant `4/pi` needs a different comparison argument: a global
derivative inequality in the same direction is false at zero. In fact
`-F_c'(0)=1/c=pi/4<1` there. The error
`F_c(x)-integral_x^infinity exp(-t^2) dt` vanishes at zero for `c=4/pi`
and at infinity; its derivative changes sign once. Proving that sign pattern
and the endpoint limits is a candidate route, not a compiled result.

Next Lean leaf: the derivative identity and nonnegative denominator facts
for arbitrary `c>0`; then the `c=2` derivative comparison and exact lower
integral bound. The upper bound must retain its separate sign-change proof.

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
