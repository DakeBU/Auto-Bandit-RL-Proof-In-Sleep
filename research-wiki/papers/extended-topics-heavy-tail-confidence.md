# Scheduled heavy-tail confidence: reviewed conservative adaptation

This page covers only `HeavyTail.scheduled_mean_tail` and
`HeavyTail.scheduled_adaptive_mean_tail` at source commit `ba81a53`.
Independent source review and a separate repair review both returned
**accepted-with-explicit-delta** on 2026-09-19. This does not accept the full
regret chain or close the Heavy-tailed topic.

## Source and exact delta

Bubeck, Cesa-Bianchi and Lugosi, *Bandits With Heavy Tail*, IEEE TIT 59(11),
2013, DOI 10.1109/TIT.2013.2277869: Assumption 1 and Figure 1 (p. 7712),
Proposition 1 proof and Lemma 1 (pp. 7713-7714).
The frozen published PDF hash is in `source-hashes.json`.

The source estimator discards observations outside the sample-indexed threshold.
With p=1+epsilon, it uses B_j=(uj/log(1/delta))^(1/p) and a displayed
one-sided confidence radius 4u^(1/p)(log(1/delta)/n)^(epsilon/p), for i.i.d.
observations with a raw absolute p-moment bound and 0<epsilon<=1.
The printed proof controls the opposite tail; reflection exchanges the tails.

The actual declarations make the following changes explicitly:

| Item | Published source | Reviewed Lean adaptation |
|---|---|---|
| Radius coefficient | 4 | 8 |
| Algorithm delta schedule | t^-2 in Figure 1 | max(t,2)^-4 |
| Confidence event | separate one-sided bounds | absolute two-sided bad event, including equality |
| Failure probability | delta per tail | 2delta, or 2t delta for selected count |
| Sample laws | i.i.d. | independent, common mean and uniform raw moment bound |
| Epsilon | (0,1] | [0,1]; no shrinking radius at zero |
| Small rounds | literal t^-2 problematic at t=1 | log(max(t,2)) defined at t=0,1 |
| Selected count | bandit count in proof | arbitrary count, event restricted to 1<=count<=t |

The published proof prints 2 sum_{s=1}^t s^-4 <= 2/t^3, false already
at t=2. A fixed-round summand t^-4 gives that order; Figure 1's t^-2 does not.
This diagnoses the displayed argument, not a refutation of its final rate or
constant 4. The local signed-centering proof explicitly retains the range 2B.
No author-issued erratum is asserted.

## Mathematical statement and proof

Let X_s be measurable independent real random variables under a probability
measure, with integrable X_s and |X_s|^(1+epsilon), common mean m and
E|X_s|^(1+epsilon)<=u, where u>0 and 0<=epsilon<=1. All these assumptions
hold for every natural index s. Set

    p=1+epsilon, q=epsilon/p, L=4 log(max(t,2)),
    B_s=(u(s+1)/L)^(1/p), a_n=u^(1/p)(L/n)^q,
    mhat_n=(1/n) sum_{s=0}^{n-1} X_s 1{|X_s|<=B_s}.

For every deterministic t>=0 and n>=1 (without requiring n<=t),

    P(|mhat_n-m| >= 8a_n) <= 2 exp(-L).

For any function N from outcomes to natural numbers,

    P*(1<=N<=t and |mhat_N-m| >= 8a_N) <= 2t exp(-L).

P* means outer probability if the count is not measurable. For measurable
counts it is ordinary probability. This finite-prefix union requires neither
independence of the selector nor a stopping-time premise. It does not prove
that a particular policy is causal or that a stopped sample is i.i.d.

To prove the fixed-prefix bound, truncation bias is at most u/B_s^epsilon,
and its second moment at most u B_s^(1-epsilon). The centered range is 2B_s.
The bounded exponential remainder gives a centered MGF bound exp(lambda^2 V)
for |lambda|b<=1, with V=sum u B_s^(1-epsilon) and b=2B_(n-1).
Using lambda=min(sqrt(L/V),1/b), with the zero-variance case handled separately,
gives a two-sided fluctuation threshold 2sqrt(VL)+bL at failure 2exp(-L).
The power-sum bound gives average bias <=p a_n, while sqrt(VL)/n<=a_n
and B_(n-1)L/n=a_n. Thus the intermediate radius is <=(p+4)a_n<=6a_n<=8a_n.
Finally the selected-count event is contained in the union of n=1,...,t fixed
prefix events. Finite subadditivity supplies the factor t.

## Actual reused proof dependencies

`scheduled_mean_tail` directly invokes `truncated_mean_tail`,
`tuned_radius_le`, threshold positivity and terminal-threshold monotonicity.
Its local producers are in `HeavyTailConfidence`, `HeavyTailTuning`,
`HeavyTailFixedTilt`, `HeavyTailTruncation`, and `HeavyTailPowerSum`.
The adaptive theorem directly reuses `scheduled_mean_tail`, Mathlib
`measureReal_mono` and `measureReal_biUnion_finset_le`, plus finite-set identities.
These are proof uses visible in the source; this page adds no formal graph edge.
The compiler-exported Lean Graph remains the authority for full term dependencies.
No conceptual functor or cross-topic bridge is certified by this review.

## Exact Lean declarations

The scoped context is namespace `BanditRLProof.HeavyTail`, with
`MeasureTheory` and `ProbabilityTheory` open. `truncate B x` retains x when
|x|<=B and returns zero otherwise. `sampleThreshold`, `confidenceLog`, and
`confidenceRadius` are exactly the B_s, L, and 8a_n definitions above.

<details>
<summary>scheduled_mean_tail</summary>

```lean
theorem scheduled_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u mean : ℝ) (t n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u) :
    μ.real {ω | confidenceRadius ε u t n ≤
      |(∑ s ∈ Finset.range n, truncate (sampleThreshold ε u t s) (X s ω)) / n - mean|} ≤
        2 * Real.exp (-confidenceLog t)
```

</details>

<details>
<summary>scheduled_adaptive_mean_tail</summary>

```lean
theorem scheduled_adaptive_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (count : Ω → ℕ) (ε u mean : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u) :
    μ.real {ω | 0 < count ω ∧ count ω ≤ t ∧ confidenceRadius ε u t (count ω) ≤
      |(∑ s ∈ Finset.range (count ω), truncate (sampleThreshold ε u t s) (X s ω)) /
        count ω - mean|} ≤ t * (2 * Real.exp (-confidenceLog t))
```

</details>

## Remaining boundary and evidence

The raw moment cannot be replaced by a centered moment without a new argument.
Counts zero or above t are excluded; the result is not uniform over all times.
Epsilon=0 yields radius 8u and supplies no positive-epsilon regret theorem.
Full regret, causal-policy transport, literal-source constants, recent-paper
proof audits, shared topic mapping and ICLR evidence remain separate work.

`runs/extended-topics-20260919/confidence-review-validation.json` binds the source,
blind packet and private reviewer reports by hash. Private review material stays
in maintenance, outside anonymous exports. The source-blind decoder, source
reviewer and separate repair reviewer were distinct actors; the formalizer did
not fill any of those roles. The merged full gate and local site checks passed;
no Lean declaration changed during this review.
