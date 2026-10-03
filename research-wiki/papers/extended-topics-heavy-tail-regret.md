# Reviewed conservative robust-UCB expected pseudo-regret

The full actual-policy-to-expected-pseudo-regret chain at `8cb5fef` received
independent source review and separate mathematical repair review on 2026-09-19.
Both verdicts are **accepted-with-explicit-delta**. This accepts the displayed
conservative adaptation, not the unchanged published algorithm/constants or
completion of the Heavy-tailed topic.

## Source, model and algorithm

Bubeck, Cesa-Bianchi and Lugosi, *Bandits With Heavy Tail*, IEEE TIT 59(11),
2013, DOI 10.1109/TIT.2013.2277869: model p.7711, Figure 1 and Proposition 1
p.7712, full proof p.7713, Lemma 1 pp.7713-7714 and Theorem 1 p.7714.
Published PDF SHA256:
`df94efa3708dab85063d6c7a04e0812f264c1c6f13a284017eb2efeed5077ef3`.

For positive finite K and 0<epsilon<=1, assume each arm's stationary reward law
has integrable raw absolute (1+epsilon)-moment bounded by known u>0. The source
Theorem 1 states the expected pseudo-regret bound

    sum_{i:Delta_i>0} [8*(4u/Delta_i)^(1/epsilon)*log n + 5*Delta_i].

Its Figure 1 uses the truncated estimator at delta=t^-2 and radius coefficient 4.
The actual Lean policy below has a different schedule and coefficient. The
printed proof's summation and gap-threshold discrepancies are explicit in
`docs/extended-topics/SOURCE-AUDIT.md`; they do not prove the source theorem false.
The bound above must not be relabeled as established by the conservative theorem.

The actual model is one fixed independent product array X(s,i), with X(s,i)
distributed according to arm i. At times 0,...,K-1 the policy selects each arm
once. Subsequently at time t it computes from observations strictly before t

    L_t=4log(max(t,2)), p=1+epsilon, q=epsilon/p,
    B_j(t)=(u*j/L_t)^(1/p),
    mhat_i(t)=sum_{j=1}^{N_i(t)} X(j-1,i)*1{|X(j-1,i)|<=B_j(t)} / N_i(t),
    index_i(t)=mhat_i(t)+8u^(1/p)*(L_t/N_i(t))^q.

The least encoded maximizing arm is selected before its next unused coordinate
is observed. Old observations are re-truncated at the current time, using their
within-arm sample ordinal. The algorithm uses epsilon,u and past observations;
it does not receive means, gaps or terminal T. Its inclusive history through n
chooses action n+1, so there is no current-reward access in the current decision.

## Exact theorem and readable proof

Let mu_i be the arm means, mu_*=max_i mu_i and Delta_i=mu_*-mu_i. For every
finite T, one fixed policy and source law satisfy

    E[sum_{t<T} Delta_{A_t}] <= sum_{i:Delta_i>0} Delta_i*(b_i(T)+2),
    b_i(T)=ceil( L_T / (Delta_i/(16u^(1/p)))^(p/epsilon) )+1.

This is expected pseudo-regret. It is not realized reward regret or a
high-probability regret guarantee. Keep the ceiling: the exact arm contribution
is Delta_i times (ceil(...) +3), not an asymptotic shorthand.

Raw moments yield genuine finite means using |x|<=1+|x|^(1+epsilon). The reviewed
confidence producers give each arm's actual adaptive-prefix failure probability
at most 2t exp(-L_t). Pathwise history-to-prefix equalities connect these
producers to the actual estimator; no stopped-sample independence is assumed.
On confidence for a best arm and a selected arm i, index maximality implies
Delta_i<=2r_i. For N_i(t)>=b_i(T) and t<=T, monotonicity of L and the strict +1
above the ceiling give 2r_i<Delta_i. Thus a large-count selection requires one
of the two arm failures, with probability at most 4t exp(-L_t).

During initialization a selected arm's prior count is zero, so no large-count
selection is possible. Deterministic count decomposition includes every early
pull in the b_i(T) budget:

    N_i(T)<=b_i(T)+sum_{t<T} 1{A_t=i and N_i(t)>=b_i(T)}.

For t>=2, 4/t^3<=1/(t-1)-1/t; the t=0 term is zero and the t=1 term is 1/4.
The finite failure sum is therefore <=2. Measurable counts are bounded by T,
so all count integrals exist and E N_i(T)<=b_i(T)+2. The exact finite
pseudo-regret/count identity finishes the bound. Zero-gap arms are split out
before any positive-gap inverse or count theorem is used.

## Source versus actual statement

| Component | Source | Actual reviewed adaptation |
|---|---|---|
| Raw moment model and epsilon | raw (1+epsilon)-moment; 0<epsilon<=1 | same; explicit integrability |
| Radius and schedule | 4; delta=t^-2 | 8; delta=max(t,2)^-4 |
| Time convention | round starts at 1 | decision time starts at 0; t corresponds to source t+1 |
| Initialization/ties | infinite unpulled index; maximizing arm | fixed round robin; least encoded maximizer |
| Regret RHS | printed explicit coefficient and +5Delta | ceiling budget +1 and tail residual +2 |
| Random model | stationary selected-arm reward | concrete fixed independent product-stream construction |
| Horizon | finite n | all natural T including 0,1 and T<K |

For T>=2, expanding the local ceiling with ceil x<=x+1 gives a looser readable
leading term 4*16^(p/epsilon)*u^(1/epsilon)*Delta^(-1/epsilon)*log T.
Its coefficient is 8*4^(1/epsilon) times the source's printed coefficient;
at epsilon=1 it is 1024 rather than 32. This algebraic comparison is not a new
Lean endpoint or an improvement claim. A smaller additive term alone does not
make the complete bound better.

## Dependencies and exact declaration

The terminal directly reuses `robust_integral_count_le`, derived first-moment
integrability, finite best-arm existence, and
`integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount`. The count proof
uses actual action measurability, UCB's prior-count indicator decomposition,
`robust_large_count_tail`, and `scheduled_tail_sum_le_two`. The source law and
pathwise transport are in `ArmStreamPolicy`, `HeavyTailHistory`, and
`HeavyTailArmLaw`; these are actual proof dependencies, not conceptual graph
arrows. No new Lean edge or cross-topic functor is claimed by this review.

<details>
<summary>Exact robust_expected_regret declaration</summary>

```lean
theorem robust_expected_regret (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (ε u : ℝ) (T : ℕ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫ stream, realMeanRegret (realKernelMean ν) (robustAction hK ε u stream) T
      ∂UCB.armStreamMeasure ν) ≤
    ∑ arm : Fin K, realMeanGap (realKernelMean ν) arm *
      (gapThreshold ε u (realMeanGap (realKernelMean ν) arm) T + 2)
```

Scoped context: namespace `BanditRLProof.HeavyTail`, `variable {K : Nat}`,
with `MeasureTheory` and `ProbabilityTheory` open. `gapThreshold` is b_i above.
The full-arm Lean sum retains zero-gap terms; totalized arithmetic defines their
threshold, but their contribution is zero and no inverse-gap reasoning is used.

</details>

## Boundaries and acceptance evidence

K=1, tied optimal arms, T=0, T=1 and T<K are included. Epsilon=0, u=0, K=0,
centered-moment-only assumptions, nonstationary laws and correlated reward
arrays are excluded. An equivalence theorem to every alternative bandit-law
representation, realized-reward expectation identity, gap-independent bound and
lower bound are not supplied here.

The nondegenerate public-root canary in `Tests/HeavyTailRegretCanary.lean`
uses two genuinely noisy arms with means 1 and 1/2, epsilon=1, u=2 and T=100.
It consumes this actual endpoint without a supplied confidence premise. Its
bounded two-point laws test a nonzero-gap stochastic instantiation; they are not
an infinite-variance example.

`runs/extended-topics-20260919/regret-review-validation.json` binds separate
blind reconstruction, source review and repair review by hash. Private reports
remain in maintenance. The reviewed source's Lean/Tests/configuration trees are
identical to the merged baseline that passed root, Tests, 434 Python tests
(7 skipped), local site build and check. The review itself changes no Lean.

Literal-source constants, full recent-source audits, shared topic mapping and all-topic ICLR evidence remain open. No
whole-topic completion, merge or deployment follows from this endpoint review.
