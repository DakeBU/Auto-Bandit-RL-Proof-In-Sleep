# Tani and Futami UAI 2026: source and repaired proof audit

The chronological checkpoints below preserve earlier findings. The latest
assembled recovery treats the actual first update separately and closes the
finite-horizon confidence-to-regret chain under an explicit contract; earlier statements
that its recurrence was still open describe the preceding checkpoints. This
is a mathematical recovery, not acceptance of the original written proof or
a Lean implementation. See the final section for the complete current scope.

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

Issues in the original written proof (replacement derivations follow):
- Eq49 drops predictable confidence indicators from an absolute signed sum;
  this need not increase that sum. Preserve the stopped process throughout.
- Eq50->51 does not justify changing vector features to adaptive scalar
  estimation-error projections while retaining the original clipping schedule.
  A direct stopped scalar replacement is derived below; its different bound
  still needs to be integrated into the full confidence recurrence.
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

## Direct stopped scalar score and corruption adapter

The vector-to-scalar invocation can be replaced by a probability bound for the
actual scalar process. Let `E_s` be a before-noise measurable event implying
the past-indexed confidence bound, and put
`d_s=<X_s/sigma_s,theta_hat_s-theta_star> 1_(E_s)`.
No assumption is made that these events hold with high probability. Retain
the original feature-based threshold and define `S_n=sum d_s h_tau_s(z_s)`
with `z_s=eta_s/sigma_s` and `h_tau` the Huber clipping function.

The actual scale, with a separately specified positive beta0 and
`beta_s=409 ell tau0 s^a+beta0` for s>=1, gives the deterministic envelope

```text
w_s^2 <= tau0 s^a/(2 sqrt(alpha) beta_(s-1)),
1+w_s^2 <= M
  := 1+max{tau0/(2 sqrt(alpha) beta0), sqrt(2)/(818 sqrt(alpha) ell)}.
```

The second estimate uses `(s/(s-1))^a<=sqrt(2)` only for s>=2 and treats
s=1 separately. It does not use beta_s in place of beta_(s-1), nor assert
the disputed first-round small-leverage floor. In fact, at alpha=8 and s>=2,
the same bound gives `w_s^2<=1/(1636 ell)<=1/64`, hence
`sigma_s>=2sqrt(2)||X_s||_(V_(s-1) inverse)`. Independent review verified
this later-round corollary; the first round remains separate under the stated
initial-value convention. Let `B_n=max_(s<=n) beta_(s-1)`.
On the whole sample space, including stopped paths,
`|d_s|<=sqrt(alpha) B_n w_s`.

Conditional mean-zero p-moments give clipping bias at most `tau_s^(1-p)`
and clipped second moment at most `tau_s^(2-p)`. Combining these with the
actual saturated-leverage sum, Holder (direct summation for p=2), and
predictability yields deterministic bias, variance and range envelopes:

```text
sum |E[d_s h_tau_s(z_s) | F_s]|
 <= sqrt(alpha M) B_n tau0^(1-p) K^(p/2) p^((2-p)/2) n^a,
sum Var[d_s h_tau_s(z_s) | F_s]
 <= alpha M B_n^2 tau0^(2-p) K^(p/2) n^(2a),
|d_s h_tau_s(z_s) - E[d_s h_tau_s(z_s) | F_s]|
 <= 2 sqrt(alpha M) B_n tau0 n^a.
```

Apply fixed-prefix Freedman to both signs with failure `delta/(2T^2)` each.
Union over n<=T costs at most delta. Substitution of the actual tau0 gives,
simultaneously for those prefixes with probability at least1-delta,

```text
|S_n| <= 4 sqrt(alpha M) B_n tau0 ell n^a.
```

For a fixed corruption upper bound C>0, the original corruption scale gives
`||X_s||_(V_(s-1) inverse)/sigma_s^2<=sqrt(K)/C`. Huber's Lipschitz property
therefore bounds the stopped difference between corrupted and clean scores
by `B_n sqrt(K) sum_(s<=n)|c_s|/C <= B_n sqrt(K)` pathwise. For C=0 every
c_s is zero and this term vanishes. Zero features contribute zero under an
explicit positive finite threshold convention. No predictability of current
corruption and no extra failure budget are required for this adapter.

These are replacement bounds, not the exact quadratic-penalty expression
printed as Eq51. They retain the explicit M and B_n factors; the original
409 radius and the full probability induction do not yet follow. Independent
math/source reports, source hashes and scope are bound in
`runs/extended-topics-20260919/tani-stopped-score-audit.json`.
This is mathematics only: no new Lean result, full regret or topic completion.

## Assembled first-round and confidence recovery

The complete derivation starts from primitive conditional centered p-moments
and the actual projected update. Let alpha=8, p=1+epsilon in (1,2],
`a=(2-p)/(2p)`, `ell=log(2T^2/delta)`, delta in (0,1/4),
`b=sqrt(lambda(2+4S^2))`, and specify beta0=b separately. For positive n,
retain `beta_n=b+409 tau0 ell n^a` and the original max-scale schedule.

For the first update, weighted projection and the rank-one inverse give
`||g_1||_(V_1 inverse)<=sqrt(alpha) tau0`, regardless of the observed reward.
The actual first scale and `sqrt(lambda)S<=b/2` then yield

```text
||theta_2-theta_star||_(V_1)^2 <= b^2+17 tau0^2 <= beta_1^2.
```

Thus no first-round small-leverage assumption or extra scale floor is needed.
For subsequent rounds the already proved floor holds. Three events are
constructed before any induction: the clean exceedance-count event, a new
weighted clipped-square event, and the stopped scalar score event restricted
to rounds2 onward. Each costs at most delta. The square event follows from
conditional p-moments and fixed-prefix Freedman applied to
`Z_s=v_s h_tau_s(eta_s/sigma_s)^2`; it gives
`sum Z_s<=4 tau0^2 ell n^(2a)`. On the score's nonzero support,
`1+w_s^2<=65/64`, so its bound is at most `12 B_n D_n`,
where `D_n=tau0 ell n^a`, `B_n=max_(s<=n) beta_(s-1)`.

On their common event, the stopped nonlinear gradient discrepancy and
corruption adapter give total generalization gap from rounds2..n at most
`54 B_n D_n`. Actual gradient stability is at most
`96 tau0^2 ell n^(2a)+3K+(3/8)sum q_s^2`, with
`q_s=<X_s/sigma_s,theta_s-theta_star>`. The conditional OMD decomposition
contributes `(1/alpha-1)sum q_s^2`; at alpha8 the combined coefficient is
negative. Telescoping from the real first-update energy gives

```text
||theta_(n+1)-theta_star||_(V_n)^2
 <= b^2+115 D_n^2+108 B_n D_n
 <= b^2+108 b D_n+44287 D_n^2
 <= (b+409 D_n)^2.
```

Only inside this induction, when its prefix confidence premise holds, is the
stopped gap equated with the actual gap. The events themselves were proved
without assuming that confidence conclusion. The resulting simultaneous
confidence probability is at least1-3delta, sufficient for the source's
weaker1-4delta probability on this finite-horizon contract. Independent
mathematical and source reviews accepted the full assembly with explicit deltas.

Qualifications remain attached: C is a fixed supplied corruption upper bound;
actions and inputs are measurably causal; beta0 is explicitly specified; zero
features use a positive finite threshold extension and are omitted from the
auxiliary noise count. K must be consistently used in both scales and
thresholds. Arbitrary positive sigma_min and causal actions are generalizations;
Lemma4.4's parameter specialization also requires sigma_min=1/sqrt(T), and
the actual UCB selector must meet the stated measurability contract. This
does not identify the two printed K definitions or certify an infinite-horizon
claim. No Lean build or declaration is added by this mathematical recovery.

Evidence: `runs/extended-topics-20260919/tani-confidence-regret-audit.json`.

## Finite regret from the actual UCB rule

The actual source UCB maximizer is used, not an arbitrary action-policy
consumer. Explicitly assume the bounded nonempty decision sets attain both
the UCB and linear-comparator maxima, the chosen UCB action is measurable,
and the optimal linear value is measurable. Boundedness alone does not
provide these facts for arbitrary decision sets. On the confidence event,
optimism gives gap at most `2 beta_(t-1)||X_t||_(V_(t-1) inverse)`.
The first gap is bounded directly by `2LS`; it does not use the disputed
first-round raw-leverage estimate.

For t>=2 the scale gives w_t^2<=1/64. Thus
`sum_(t=2..T) w_t^2<=2 log(det V_T/det V_0)<=2K`.
Partition these rounds by the active term in the actual max-scale. Fixed tie
assignment for this analysis changes neither the policy nor the scale:

- Moment/minimum-scale rounds contribute at most
  `sqrt(2K)*sqrt(sum nu_t^2+T sigma_min^2)` to `sum sigma_t w_t`.
- Confidence-scale rounds have the exact identity
  `w_t^(-2)=2sqrt(alpha) beta_(t-1)/(tau0 t^a)`.
  It is at most `2sqrt(alpha)(b/tau0+409ell)`. Their count is bounded using
  the raw-leverage sum, and each `sigma_t w_t<=L/sqrt(alpha lambda)`.
  This yields `4KL/sqrt(lambda)*(b/tau0+409ell)`.
- Corruption-scale rounds satisfy
  `sigma_t w_t=sqrt(alpha) C w_t^2/sqrt(K)`, hence contribute at most
  `2sqrt(alpha) C sqrt(K)`. This group is empty when C=0.

Consequently, on the same event of probability at least1-3delta,

```text
R_T <= 2LS + 2sqrt(alpha) beta_T * [
  sqrt(2K)*sqrt(sum_(t=1..T)nu_t^2+T sigma_min^2)
  + 4KL/sqrt(lambda)*(b/tau0+409ell)
  + 2sqrt(alpha) C sqrt(K) ].
```

For lambda=d, sigma_min=1/sqrt(T), alpha8, delta=1/(8T), fixed L,S and
either consistently chosen source K, this has the source order
`O_tilde(d T^a sqrt(sum nu_t^2)+d T^a max(1,C))`, with probability at least
1-1/T. The finite initial residual remains visible above. Bounding the
confidence-scale term uses the exact cancellation
`K b/tau0=b sqrt(K/2) ell^(1/p)/(log(3T))^a`; no lower bound on K is assumed.

Independent mathematical and source reviews accepted this full composition
with the preceding contract qualifications. It is a new proof of the
qualified endpoint, not validation of the original Appendix B/C derivation,
literal equivalence for arbitrary bounded decision sets, or a Lean theorem.
Huang published-supplement identity, implementation/measurable-selector
construction, and the global topic/ICLR obligations are separate. No new
Lean gate, main merge, deployment or whole-topic completion is asserted.


## Huang v3 dependency checkpoint (2026-09-20)

The separate [Huang score audit](HUANG23-SOURCE-AUDIT.md) reconstructs C.4,
C.5 and C.2 from primitive conditional moments and the actual Gram process.
It replaces extraction of random predictable MGF factors by a compensated
exponential, and replaces the invalid horizon-to-prefix calibration by a
direct square-term bound. The constants4 and8 are preserved on an explicit
finite horizon. Independent mathematical and source reviews accept this repair with the
explicit contract deltas. Evidence: `runs/extended-topics-20260919/huang-v3-dependency-audit.json`.

This vector-score result does not itself permit the adaptive scalar
projection in the original Tani argument. The direct stopped scalar proof
above remains necessary. The fixed source is arXiv2306.06836v3, March2024;
identity with the NeurIPS2023 published supplement is still unverified.
No complete Huang curvature/regression/RL theorem or Lean acceptance follows.
