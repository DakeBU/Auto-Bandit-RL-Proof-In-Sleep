# Gaussian Mills-Ratio Tail Bounds

Status: both exact integral bounds pass focused Lean and module build;
Gaussian probability rescaling now compiles in standardized coordinates;
printed denominator normalization now also compiles; full integration validation
and synchronization of the older chapter-wide evidence remain pending.

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

The first focused Lean check of `LowerBounds/GaussianMillsRatio.lean` passed:
`gaussianMillsComparison_denominator_pos` and
`hasDerivAt_gaussianMillsComparison` retain only `c>0` and work for every real
`x`. The `c=2` comparison `gaussianMillsComparison_lower_derivative_bound`
also holds for every real `x`. Root export and external canaries have been
added; their full integration gate is still pending for this extension.

`tendsto_gaussianMillsComparison` now proves `F_c -> 0` for `c>0` by
squeezing against `1/x` on the eventual positive half-line.
`gaussianMills_lower_integral` passes focused Lean with the exact source
lower expression and the sole premise `x>=0`. Its proof obtains derivative
integrability from the nonpositive derivative and limit, evaluates that
integral, and compares its negative with the integrable Gaussian kernel.

The upper-branch algebra now passes focused Lean:
`gaussianMills_sign_iff`, `gaussianMills_sign_threshold`,
`gaussianMillsErrorDerivative_factor`, and
`gaussianMillsErrorDerivative_nonneg_iff` identify the sole nonnegative
threshold `(c-1)/sqrt(2-c)` for `1<c<2`, `x>=0`. The error derivative here
is connected by `hasDerivAt_gaussianMillsError` to the finite-integral error
`F_c(x) + integral_0^x exp(-t^2) dt - sqrt(pi)/2`.
`gaussianMillsErrorDerivative_source_nonneg_iff` specializes the threshold
to `c=4/pi`, using `Analysis.Real.Pi.Bounds`. The complete module build
passes (3345 jobs). `gaussianMillsError_source_zero`,
`tendsto_gaussianMillsError`, and `gaussianMillsError_source_nonneg` now
close the endpoint and piecewise monotonicity argument.
`gaussian_integral_split` identifies the finite plus improper integrals.
`gaussianMills_upper_integral` proves the exact upper half of Eq. (13.4).

`gaussianReal_zero_standardized_tail` now identifies the exact centered
Gaussian tail as the normalized source integral at `a/sqrt(2*v)` for `v>0`.
`gaussianReal_zero_mills_bounds` transfers both inequalities through this
identity. `gaussianSampleMeanZeroErrorProbability_mills_bounds` applies them
to the existing error-probability definition with `n>0`, `Delta>0` and
`z=(Delta/2)/sqrt(2/n)`. Both modules build (3559 jobs).

`gaussianMills_expression_rescale` and
`gaussianSampleMeanZeroErrorProbability_source_bounds` now compile the exact
printed Eq. (13.1), with `q=n*Delta^2`, exponent `-q/8`, and denominator
constants `16` and `32/pi`. The only premises are `n>0` and `Delta>0`.
Full integration gates and chapter-wide evidence synchronization remain pending.

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

## Original first executable leaf (now compiled)

Prove a generic real-analysis theorem for `x >= 0` bounding
`integral (fun t : Real => Real.exp (-t^2))` over `Set.Ioi x` in both source
directions.  Keep denominator positivity explicit, then derive the standard
normal-tail version and finally the `N(0,1/n)` midpoint specialization.

## Regularity and nonclaims

The integrand's measurability and integrability are available from Mathlib's
Gaussian integral development. This card is not itself proof evidence;
the compiled declarations identified above establish Eq. (13.1).
The Chernoff companion remains distinct from both exact source bounds.
