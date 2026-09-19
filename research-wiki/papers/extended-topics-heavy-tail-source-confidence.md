# Source constant-four truncated confidence

Bubeck, Cesa-Bianchi and Lugosi, *Bandits With Heavy Tail*, IEEE TIT 59(11),
2013, DOI 10.1109/TIT.2013.2277869, Lemma 1 pp.7713-7714 and Assumption 1 p.7712.
The frozen published PDF hash is recorded in `docs/extended-topics/source-hashes.json`.
This page concerns the source estimator and confidence constant, not the published
algorithm's regret bound. Independent semantic review is recorded separately.

## Source contract and assumptions

Let X_1,...,X_n be i.i.d. real observations with mean m, n>=1, u>0,
0<epsilon<=1, E|X|^(1+epsilon)<=u and 0<delta<1. Put

    L=log(1/delta), p=1+epsilon, q=epsilon/p,
    B_j=(uj/L)^(1/p),
    mhat=(1/n) sum_{j=1}^n X_j*1{|X_j|<=B_j}.

The source Lemma 1 asserts mhat<=m+4u^(1/p)(L/n)^q with probability at
least 1-delta. Its displayed proof controls the opposite tail, which reflection
exchanges. The actual Lean statements prove both signed bad-event bounds,
separately at delta and at the same radius four, for every delta in (0,1).
Truncation discards an outlier entirely; it is not clipping. The denominator
remains n and observations at threshold equality are retained.

The actual assumptions explicitly include measurable observations, integrable
first and raw p moments, a common mean, independence and a uniform raw-moment
bound. Identical distribution is relaxed: only the common mean and moment bound
are used. Assumptions are imposed on an infinite sequence, with the first n
terms consumed. The finite source experiment embeds into an i.i.d. stream;
no policy or random-count claim is attached to this theorem.

| Semantic component | Classification | Actual difference |
|---|---|---|
| Sample-index thresholds, raw moment, coefficient4, arbitrarydelta | same | unchanged |
| Measurability and integrability | source-implicit | explicit real-integral prerequisites |
| Independent common-mean sequence rather than identical laws | generalization | no identical-law premise required |
| Infinite index family rather than finite sample notation | API-limitation | full-family hypotheses; conclusion uses first n only |
| Closed bad event error>=radius | generalization | stronger than source's error>radius complement |
| Two separately proved signed tails | generalization | reflection; each has failure delta, not a claimed joint delta |
| Algorithm schedule and regret constants | unresolved | these declarations make no new algorithm guarantee |

## Proof preserving the constant

Write Z_j=X_j 1{|X_j|<=B_j}. The raw moment implies
|EZ_j-m|<=u/B_j^epsilon and E Z_j^2<=u B_j^(1-epsilon).
Instead of applying an exponential remainder to the centered variable, apply
it to lambda Z_j with |lambda|B_j<=1:

    E exp(lambda(Z_j-EZ_j))
    = exp(-lambda EZ_j) E exp(lambda Z_j)
    <= exp(-lambda EZ_j)(1+lambda EZ_j+lambda^2 E Z_j^2)
    <= exp(lambda^2 E Z_j^2).

Thus the full raw-variable tilt 1/B is allowed. This does not assert the false
signed-range estimate |Z_j-EZ_j|<=B_j, and uses the raw second moment rather
than variance in the exponent. Exponential integrability comes from bounded Z_j.
The EXP3 exponential-remainder lemma is actually reused at this step.

Let B=(un/L)^(1/p), a=u^(1/p)(L/n)^q and V=sum u B_j^(1-epsilon).
Power-sum control and the scale identities give

    total bias<=p*n*a, V<=B^2*L, B*L=n*a.

Independence multiplies MGFs. At lambda=1/B, a centered upper-sum deviation
2B L has exponent at most -2L+V/B^2<=-L. Adding bias requires radius
(p+2)a<=4a since p<=2. Division by positive n gives the stated upper tail.
Reflect X to -X: truncation is odd and the absolute raw moment is unchanged.
The same theorem therefore supplies the lower tail. Finally exp(-log(1/delta))
is exactly delta. No confidence event or MGF is supplied as an endpoint premise.

## Actual proof reuse and graph boundary

`bounded_centering_mgf_unshifted` reuses the EXP3 remainder and Mathlib integral
monotonicity, exponential identities and integrability bounds.
`source_centered_sum_upper_tail` uses this MGF, `integral_sq_truncate_le`,
`independent_sum_mgf` and its Chernoff interface. The bias side reuses
`power_threshold_bias_sum`, `power_scale_bias`, `power_bias_normalization`,
`threshold_scale_identity` and `threshold_variance_identity`, plus
`integral_truncate_bias_le`. The lower theorem reuses the upper theorem by
reflection, not a copied concentration proof.

The compiler graph receives these declarations and actual imports. This is an
improved local probability producer; no conceptual functor or new cross-setting
bridge is certified. Existing policy and regret declarations remain unchanged.

## Exact Lean statements

Scoped context: namespace `BanditRLProof.HeavyTail`, open `MeasureTheory`
and `ProbabilityTheory`. `sourceTruncationThreshold epsilon u L s` is exactly
(u(s+1)/L)^(1/(1+epsilon)); `truncate` is the outlier-discarding function above.

<details>
<summary>source_truncated_mean_upper_tail</summary>

```lean
theorem source_truncated_mean_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u δ mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 4*u^(1/(1+ε))*(Real.log (1/δ)/n)^(ε/(1+ε)) ≤
      (∑ i ∈ Finset.range n,
        truncate (sourceTruncationThreshold ε u (Real.log (1/δ)) i) (X i ω))/n - mean}
      ≤ δ
```

</details>

<details>
<summary>source_truncated_mean_lower_tail</summary>

```lean
theorem source_truncated_mean_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u δ mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 4*u^(1/(1+ε))*(Real.log (1/δ)/n)^(ε/(1+ε)) ≤
      mean - (∑ i ∈ Finset.range n,
        truncate (sourceTruncationThreshold ε u (Real.log (1/δ)) i) (X i ω))/n}
      ≤ δ
```

</details>

## Remaining boundary

The endpoint excludes n=0, epsilon=0, u=0 and delta outside (0,1). The internal
positive-L theorem also permits epsilon=0 but then its radius does not shrink.
The result is for each fixed n,delta, not a simultaneous confidence sequence.
Raw moments cannot be replaced silently by central moments. No unchanged
published regret constant, gap-independent result or topic completion follows.

The public-root canary consumes the upper theorem on one thousand genuinely random
observations taking values0 and2 with equal probability, mean1, second moment2
and delta=1/20. Both signed endpoints and the MGF are included in its axiom
checks. Shared gates and the distinct blind/source/repair roles are bound in
`runs/extended-topics-20260919/source-confidence-validation.json`.
