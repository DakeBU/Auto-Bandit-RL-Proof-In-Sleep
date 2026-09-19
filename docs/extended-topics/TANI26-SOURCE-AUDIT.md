# Tani and Futami UAI 2026: local proof audit

Source: Robust and Computationally Efficient Linear Contextual Bandits under
Adversarial Corruption and Heavy-Tailed Noise, PMLR337:6645-6676.
PDF SHA256: d94bd094a16744dd9bd0dfee302a2ff4be58c2540fe3027767f938f53530686e.
Independent source reviewer A read the full supplied model/algorithm and relevant
proof appendices B-D, including rendered checks of pp6667,6670,6672.
External Wang2025/Huang2023 dependencies are only partially audited below; no
complete transitive proof certification, code reproduction or Lean acceptance
is asserted.

The model has conditional mean-zero (1+epsilon)-moment noise, epsilon in (0,1],
known moment scales, known horizon and a supplied corruption budget or valid
upper bound. Infinite variance is permitted when epsilon<1. The procedure is
Huber/projected OMD with a leverage-dependent scale, not BCL scalar hard
truncation. The endpoint is high-probability conditional-mean pseudo-regret.
Unknown-budget corollaries require available valid upper bounds; epsilon remains
an input. Constant update cost is only in horizon, not dimension or arm oracle.

Unresolved written-proof obligations:
- Eq49 drops predictable confidence indicators from an absolute signed sum;
  this need not increase that sum. Preserve the stopped process throughout.
- Eq50->51 does not justify changing vector features to adaptive scalar
  estimation-error projections while retaining the original clipping schedule.
- p6670 substitutes beta_t for beta_(t-1) to assert a leverage floor; the
  initial beta0 can fail to supply that floor. A separate initialization proof
  or explicit algorithm change is required.
- Eq62 omits a factor alpha in w_t^(-2). Correcting this fixed factor can
  preserve the asymptotic rate but changes the displayed constant.
- Huber kink, zero-action, zero-corruption, optimization attainment and finite
  horizon conventions need explicit treatment.

These findings concern the supplied proof; they do not establish a false final
theorem. The source is a distinct future conditional-noise contextual extension,
not a replacement proof of BCL's original scalar algorithm/regret coefficient.
Detailed derivations and the initialization parameter check are recorded in
private review-20260919/tani26-full-audit.md, hashed in the run receipt.

## External-dependency checkpoint: quarter-threshold transfer

Pinned [Huang arXiv v3](https://arxiv.org/pdf/2306.06836v3), dated March 2024,
SHA256 84ea805fae998deeea63273932b207ac5edd0c10616c2f1ba1f260aec4ff527f.
Its identity with the NeurIPS2023 supplement remains unverified.
The appendix C.12/I.1 route, with explicit predictable scales and leverage
budget, yields a finite-horizon threshold-count coefficient
`r^(1+epsilon) + sqrt(2*r^(1+epsilon)) + 2/3` at threshold `tau/r`.
For r=4 and epsilon<=1, the direct bound is at most `67/3`;
the displayed substitution does not establish Tani Eq43's smaller `65/3`.
Independent mathematical review accepted this bounded derivation and explicit
limitation. It is not a counterexample to Eq43 or a repaired final regret proof.
The stronger actual leverage producer below now recovers the bounded count
edge; downstream confidence and regret remain open.

The [official Wang2025 source](https://proceedings.mlr.press/v267/wang25et.html)
is pinned with SHA256
0e0f6f0941884f0b9da758a405e51b9564b04dc46b6d5009cae9810f0f4093e2.
Initial inspection verified Lemma7's deterministic determinant/trace algebra.
Its Eq30–31 also removes stopped indicators and invokes a scalar conversion;
these steps do not supply the missing justification identified above.
Full concentration dependency acceptance remains pending; the bounded
quadratic OMD specialization is treated below.

Evidence: `runs/extended-topics-20260919/tani-external-dependency-audit.json`.
This checkpoint adds no Lean declaration or fresh build result.

## Actual Gram budget recovers the quarter-threshold count

Independent mathematical and source reviews accepted the following replacement
derivation with explicit scope differences. Put
`a_s=X_s/(sqrt(alpha)*sigma_s)`, so the actual source update is
`V_s=V_(s-1)+a_s a_s^T` and `w_s^2=a_s^T V_(s-1)^(-1)a_s`.
For every `q>=0`, `q/(1+q)<=log(1+q)`. Rank-one determinants telescope, and
trace/AM-GM with `||X_s||<=L`, `sigma_s>=sigma_min` gives

```text
sum_(s<=n) w_s^2/(1+w_s^2)
  <= log(det V_n/det V_0)
  <= d log(1+L^2 T/(alpha sigma_min^2 lambda d)) = kappa_A,  n<=T.
```

This producer needs no small-leverage assumption or confidence event. Fix a
finite deterministic `K>=kappa_A`, and use that same K in the source threshold
`tau0=sqrt(2K)(log(3T))^((2-p)/(2p))/ell^(1/p)`, where
`p=1+epsilon` and `ell=log(2T^2/delta)`. Predictable scales satisfying
`sigma_s>=nu_s` normalize the conditional p-moment to at most one.
Conditional Markov, Holder (direct summation at p=2) and the budget above give

```text
sum_(s<=n) E[1{|eta_s/sigma_s|>tau_s/r} | before-noise history]
  <= (r/sqrt(2))^p ell.
```

The centered indicators have absolute value at most one and conditional
variance sum bounded by this predictable mean sum. Fixed-prefix Freedman,
with failure `delta/(2T^2)`, and a union over `n=1,...,T` give a simultaneous
count bound `(B+sqrt(2B)+2/3)ell`, `B=(r/sqrt(2))^p`.
For r=4 and p<=2, B<=8, so the coefficient is at most **38/3 < 65/3**.
Thus Eq43's numerical bound is recovered by a stronger argument; the earlier
coarse substitution gap is not a remaining obstruction to this bounded edge.

Material qualifications: the corruption budget is a fixed known upper bound,
actions/estimates are measurably causal, and the bound concerns only prefixes
up to T. Algorithm1's kappa_A and Lemma4.4's larger denominator-four kappa
remain distinct schedules; either works when used consistently. The literal
finite-threshold reading excludes zero features; extending their threshold
to infinity with a zero count indicator is an explicit convention and does
not itself define a complete extended Huber update. The argument controls
the saturated sum, not `sum w_s^2`; the initial-floor issue for the separate
stability proof remains open. No Lean implementation is claimed.

Evidence: `runs/extended-topics-20260919/tani-sharp-producers-audit.json`.

## Actual quadratic OMD decomposition

The finite-dimensional specialization of Tani B.1 / Wang Lemma3 can be proved
directly from the actual constrained quadratic update, without assuming the
general Banach-space proximal lemma. The objective
`<g_s,theta> + ||theta-theta_s||_(V_s)^2/2` has a unique minimizer on the
closed radius-S ball: the ball is compact and convex, and V_s is positive
definite. Feasible one-sided directional derivatives at that minimizer give
the three-point inequality, including the negative squared step term.

On each stipulated confidence event, the original scale term with
`beta_(s-1)` puts the noiseless residual within `tau_s/2`. Thus its Huber
gradient is exactly `gtilde_s=X_s X_s^T(theta_s-theta_star)/sigma_s^2`;
there is no need to differentiate at a Huber kink. Set
`Q_s=<X_s,theta_s-theta_star>^2/sigma_s^2` and
`D_s=<gtilde_s-g_s,theta_s-theta_star>`. The projection inequality, dual-metric
Young inequality and actual matrix update give

```text
||theta_(s+1)-theta_star||_(V_s)^2
 <= ||theta_s-theta_star||_(V_(s-1))^2
    + ||g_s||_(V_s inverse)^2 + 2 D_s + (1/alpha-1) Q_s.
```

The time-indexed energies telescope. Initialization is at most `4 lambda S^2`
for two arbitrary feasible points, or `lambda S^2` for the actual zero start.
This matches the source's conservative decomposition. It is conditional on
all required confidence events; it neither establishes those events nor
removes a stopping indicator from a signed random sum. Pointwise attainment
does not by itself prove measurable optimizer dependence. Zero features still
require a defined threshold convention. Separate mathematical/source review
and the exact remaining boundaries are recorded in the same audit receipt.
No full confidence/regret acceptance or Lean implementation is asserted.
