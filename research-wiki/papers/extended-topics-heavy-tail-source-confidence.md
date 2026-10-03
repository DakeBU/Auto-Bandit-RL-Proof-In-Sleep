# Source constant-four truncated confidence

Bubeck, Cesa-Bianchi and Lugosi, *Bandits With Heavy Tail*, IEEE TIT 59(11),
2013, DOI 10.1109/TIT.2013.2277869, Lemma 1 pp.7713-7714 and Assumption 1 p.7712.
The frozen published PDF hash is recorded in `docs/extended-topics/source-hashes.json`.
This page concerns the source estimator and confidence constant, not the published
algorithm's regret bound. Independent source review and separate proof-method review accept these
statements with the explicit generalizations below.

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
| Sample-index thresholds, raw moment, coefficient 4, arbitrary delta | same | unchanged |
| Measurability and integrability | source-implicit | explicit real-integral prerequisites |
| Independent common-mean sequence rather than identical laws | generalization | no identical-law premise required |
| Infinite index family rather than finite sample notation | API-limitation | full-family hypotheses; conclusion uses first n only |
| Closed bad event error>=radius | generalization | stronger than source's error>radius complement |
| Two separately proved signed tails | generalization | reflection; each has failure delta, not a claimed joint delta |
| Algorithm schedule and regret constants | separate results | source-policy confidence and corrected regret accepted; literal coefficient has a finite Lean counterexample, documented in their separate readers |

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
The coefficient-one display is now a weakening of the sharper Mathlib remainder
route below; the historical EXP3 remainder is no longer a direct proof dependency.

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

`bounded_centering_mgf_unshifted` now weakens
`bounded_centering_mgf_unshifted_sharp`, whose scalar remainder is derived from
Mathlib `Real.exp_bound` at order two. Integral monotonicity, exponential identities
and integrability bounds are reused as before.
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

<details>
<summary>Shared unshifted MGF interface</summary>

```lean
theorem bounded_centering_mgf_unshifted {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (B v tilt : ℝ) (hYm : Measurable Y) (hbound : ∀ ω, |Y ω| ≤ B)
    (hv : (∫ ω, (Y ω)^2 ∂μ) ≤ v)
    (hsmall : |tilt| * B ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun ω => Y ω - ∫ ω, Y ω ∂μ) tilt (tilt^2 * v) μ
```

</details>

## Remaining boundary

The endpoint excludes n=0, epsilon=0, u=0 and delta outside (0,1). The internal
positive-L theorem also permits epsilon=0 but then its radius does not shrink.
The result is for each fixed n,delta, not a simultaneous confidence sequence.
Raw moments cannot be replaced silently by central moments. No unchanged
published regret constant, gap-independent result or topic completion follows.

The public-root canary consumes the upper theorem on one thousand genuinely random
observations taking values 0 and 2 with equal probability, mean 1, second moment 2
and delta=1/20. Both signed endpoints and the MGF are included in its axiom
checks. Shared gates and the distinct blind/source/repair roles are bound in
`runs/extended-topics-20260919/source-confidence-validation.json`.

The compiled export in `source-confidence-reuse.json` identifies 19 direct
project proof references from the new modules to five pre-existing source
modules whose Git blobs are unchanged from the comparison base. It separates
these from type-only and external references. These counts describe actual
reuse, not novelty, saved effort or causal efficiency.


## Sharper probability at the identical radius (2026-09-19)

The actual source Lemma 1 asks for failure delta. A new strengthening proves each
signed closed bad event at the very same radius and thresholds has probability
at most exp(-5L/4). This exponent is our derived strengthening, not the paper's
printed statement. The fixed positive sample size and common-mean independent
sequence assumptions remain exactly those above, with epsilon=0 additionally
allowed by the log-confidence interface. Positive u,L,n are required.

Mathlib's order-two exponential remainder gives, for every signed |x|<=1,

    |exp(x)-(1+x)| <= (3/4)*x^2.

Apply this before centering to obtain

    E exp(lambda(Z-EZ)) <= exp((3/4)*lambda^2 E Z^2).

Independence and the same V<=B^2 L bound give, at lambda=1/B,

    P(sum(Z_j-EZ_j)>=2BL) <= exp(-2L+(3/4)V/B^2) <= exp(-5L/4).

The bias budget and radius-four inclusion are unchanged. Reflection gives the
lower signed event. The previous exp(-L) and arbitrary-delta public interfaces
are explicit weakenings of this stronger producer. No centered variance or
false centered-range assumption was inserted.

For the proposed original schedule L_t=2log(t+1), this fixed-prefix expression
is (t+1)^(-5/2). A finite union over t possible counts and a telescoping bound
would make the total failure budget finite. That full adaptive-policy assembly
is a next obligation, not a conclusion of these declarations. The deterministic
twice-radius regret coefficient issue also remains separate.

The following declarations are exact, including proofs. Their direct local
parents are the sharper MGF producer, independent_sum_mgf, the existing
truncation moment/bias bounds and source threshold scale lemmas. No new
conceptual functor is claimed.

<details>
<summary>source_truncated_mean_upper_tail_log_sharp</summary>

```lean
theorem source_truncated_mean_upper_tail_log_sharp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u L mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u) (hL : 0 < L)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 4*u^(1/(1+ε))*(L/n)^(ε/(1+ε)) ≤
      (∑ i ∈ Finset.range n, truncate (sourceTruncationThreshold ε u L i) (X i ω))/n - mean}
      ≤ Real.exp (-(5/4 : ℝ)*L) := by
  let B := (u*n/L)^(1/(1+ε))
  let R := u^(1/(1+ε))*(L/n)^(ε/(1+ε))
  let bias := ∑ i ∈ Finset.range n, u/(sourceTruncationThreshold ε u L i)^ε
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < 1+ε := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hq : 1-1/(1+ε) = ε/(1+ε) := by field_simp; ring
  have hBL : B*L = n*R := by
    dsimp [B, R]
    rw [threshold_scale_identity u L n (1/(1+ε)) hu.le hL hN, hq]
  have hbias := sourceThreshold_bias_average ε u L hε0 hu hL n hn
  have hbias' : bias / n ≤ (1+ε)*R := by simpa only [bias, R, mul_assoc] using hbias
  have hbudget : bias+2*B*L ≤ n*(4*R) := by
    have hb := (div_le_iff₀ hN).mp hbias'
    have hεR := mul_nonneg (sub_nonneg.mpr hε) (mul_nonneg hN.le hR)
    nlinarith [hBL]
  have hb : |∑ i ∈ Finset.range n,
      ((∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)-mean)| ≤ bias := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h := integral_truncate_bias_le μ (X i) _ ε u
      (sourceThreshold_pos ε u L hu hL i) hε0 (hXm i) (hX i) (hm i) (hraw i)
    rw [hmean i, abs_sub_comm] at h
    exact h
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (source_centered_sum_upper_tail_sharp μ X ε u L n hn hXm hi hε0 hε hu hL hm hraw)
  intro ω hw
  simp only [Set.mem_setOf_eq, mul_assoc] at hw
  change 4*R ≤ _ at hw
  change 2*B*L ≤ _
  have hid : (∑ i ∈ Finset.range n, truncate (sourceTruncationThreshold ε u L i) (X i ω)) - n*mean =
      (∑ i ∈ Finset.range n, (truncate (sourceTruncationThreshold ε u L i) (X i ω) -
        ∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)) +
      ∑ i ∈ Finset.range n, ((∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)-mean) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hw' : n*(4*R) ≤
      (∑ i ∈ Finset.range n, truncate (sourceTruncationThreshold ε u L i) (X i ω))-n*mean := by
    have hh := (mul_le_mul_of_nonneg_right hw hN.le)
    rw [sub_mul, div_mul_cancel₀ _ hN.ne'] at hh
    nlinarith
  have hm' := (le_abs_self (∑ i ∈ Finset.range n,
      ((∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)-mean))).trans hb
  linarith
```

</details>

<details>
<summary>source_truncated_mean_lower_tail_log_sharp</summary>

```lean
theorem source_truncated_mean_lower_tail_log_sharp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u L mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u) (hL : 0 < L)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 4*u^(1/(1+ε))*(L/n)^(ε/(1+ε)) ≤
      mean - (∑ i ∈ Finset.range n,
        truncate (sourceTruncationThreshold ε u (L) i) (X i ω))/n}
      ≤ Real.exp (-(5/4 : ℝ)*L) := by
  have h := source_truncated_mean_upper_tail_log_sharp μ (fun i ω => -X i ω) ε u L (-mean) n hn
    (fun i => (hXm i).neg) (hi.comp (fun _ x => -x) (fun _ => measurable_neg))
    hε0 hε hu hL (fun i => (hX i).neg)
    (fun i => by rw [integral_neg, hmean i])
    (fun i => by simpa only [abs_neg] using hm i)
    (fun i => by simpa only [abs_neg] using hraw i)
  simpa only [truncate_neg, Finset.sum_neg_distrib, neg_div, sub_neg_eq_add, neg_add_eq_sub]
    using h
```

</details>

Independent packet D review: decoder B reconstructed the actual signed
statements; source reviewer A accepted the stated strengthening and explicit
assumption deltas; separate repair reviewer A accepted the actual MGF/bias/
reflection proof. These reviews do not certify the original adaptive policy.
The earlier compiled-reuse receipt binds abf4d27; it is historical after this
refactor and must not be used as the new proof's direct-dependency inventory.
