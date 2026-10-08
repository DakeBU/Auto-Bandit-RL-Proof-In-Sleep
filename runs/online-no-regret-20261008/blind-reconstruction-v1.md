# Neutral reconstruction B001-B012

Actor /root/osd_blind. Requested GPT-6 Astra / medium; no escalation. Runtime model/effort are not independently attested. This is a reused actor with prior neutral-packet work on current-support policies, scalar losses, linearization, scalar tuning, scaling, finite-prefix/state/domain statements, and staged lower-bound interfaces. Background may therefore be inherited; this is not an absolute-blind, first-exposure, human, or external review. For this reconstruction only the new neutral-packet-v1.lean and neutral-inputs-v1.json were read. No source, contract, public module, proof, alias map or existing review was inspected.

## Six explicit context definitions

1. For any type X:Type v, real losses \(\ell:\mathbb N\to X\to\mathbb R\), supplied predictions \(p:\mathbb N\to X\), comparator \(u:X\), and natural N,
\[
r(\ell,p,u,N)=\sum_{t=0}^{N-1}\ell_t(p_t)-\sum_{t=0}^{N-1}\ell_t(u).
\]
This is signed regret against one fixed comparator, not an infimum or absolute value. Write \(s_u(N)=r(\ell,p,u,N)/N\). Real coercions of N are implicit in real arithmetic. At N=0 both sums are empty and total real division gives s_u(0)=0.

2. \(\operatorname{upper}(V,\ell,p)\) means
\[
\forall u\in V,\ \forall\varepsilon>0,\quad
\forall^{\mathrm{eventually}}N\in\mathbb N,\quad s_u(N)\le\varepsilon.
\]
Equivalently for each fixed u and positive epsilon there exists an eventual threshold K such that every N>=K satisfies that inequality. Thresholds may depend on u and epsilon. There is no absolute-value bound, lower bound, or assertion that a real limit exists.

3. \(\operatorname{limit}(V,\ell,p)\) means
\[
\forall u\in V,\ \exists a\in\mathbb R,\quad a\le0\ \land\
s_u(N)\longrightarrow a\quad(N\to\infty).
\]
This is an ordinary finite REAL limit, comparator by comparator. The limit may be negative and may depend on u. It is stronger than a one-sided eventual upper property when convergence is not separately known. It does not allow an infinite limit or merely a limsup.

4. The explicitly defined scalar sequence is
\[
h_N=\begin{cases}N,&N\bmod2=0,\\0,&N\bmod2\ne0.\end{cases}
\]
It is defined for every natural N; in particular h_0=0.

5. The concrete real loss is
\[
f_t(x)=(h_{t+1}-h_t)x.
\]
Its domain is ALL real x; comparator interval restrictions do not redefine that domain. The time-varying coefficients are allowed to be negative and to grow. No bounded-loss hypothesis appears. The concrete prediction stream used below is p_t=0.

6. For a total real target stream y,
\[
q_t(y)=\begin{cases}1/2,&t=0,\\
\displaystyle\frac{\sum_{i=0}^{t-1}y_i}{t},&t>0.
\end{cases}
\]
This explicitly defines a midpoint-initialized running-prefix-mean predictor. Its positive-time formula uses only strict-past targets, and its time-zero branch is fixed. No future or comparator input appears in that expression. There is no external algorithm identity supplied; recognizing an external named algorithm is not part of this reconstruction. The general p in r/upper/limit remains completely arbitrary and has no causality constraint. The code provides the formula of q, but no separately stated prefix-invariance theorem among these twelve targets. There is no probability space, randomized learner, filtration, or independent-data assumption.

All targets are closed definitions of Prop. They describe propositions; this report neither checks their proofs nor treats the type definitions as proofs. In the seven slots below, symbols \(\ell\) and \(\beta\) avoid confusing arbitrary losses/bounds with the specific context f and q.

## B001

1. **Objects.** Arbitrary X:Type v, V subset X, real loss stream ell, prediction stream p, comparator u and real a.
2. **Quantifier.** First every X,V,ell,p; assume upper; then every u in V and EVERY real candidate limit a.
3. **Assumptions.** upper(V,ell,p) and actual ordinary convergence \(s_u(N)\to a\) for this comparator.
4. **Conclusion.** Any existing real limit must be nonpositive:
\[
\forall X,V,\ell,p,\quad \operatorname{upper}(V,\ell,p)\Rightarrow
\forall u\in V,\forall a\in\mathbb R,\quad
[s_u(N)\to a]\Rightarrow a\le0.
\]
5. **Constants/normalization.** Division by N, eventual threshold as N→infinity, comparison with zero; no rate.
6. **Information/probability.** Deterministic limit constraint, with no restriction on the supplied prediction rule.
7. **Boundary.** Does NOT assert existence of a limit. Empty V gives vacuous comparator quantifiers; finite initial indices including N=0 do not affect convergence.

## B002

1. **Objects.** Arbitrary X,V,ell,p as above.
2. **Quantifier.** Every such quadruple; one implication.
3. **Assumptions.** limit(V,ell,p), providing a finite nonpositive limiting value for each comparator.
4. **Conclusion.** This implies the one-sided upper property:
\[
\forall X,V,\ell,p,\quad\operatorname{limit}(V,\ell,p)\Rightarrow\operatorname{upper}(V,\ell,p).
\]
5. **Constants/normalization.** Both properties normalize by the same N. The limit is allowed to be below zero, not necessarily equal zero.
6. **Information/probability.** Ordinary real convergence implies an eventual upper tolerance for each comparator; no probability.
7. **Boundary.** No converse without more hypotheses is asserted. Does not assert convergence of absolute regret, uniformity over comparators, or causal predictions.

## B003

1. **Objects.** Arbitrary X,V,ell,p and comparatorwise normalized regret sequences.
2. **Quantifier.** For every X,V,ell,p, first assume existence of SOME real limit for EVERY u in V; then assert equivalence.
3. **Assumptions.** \(\forall u\in V,\exists a\in\mathbb R,\ s_u(N)\to a\), with no sign restriction in this premise.
4. **Conclusion.** Under that separate convergence assumption, the two properties coincide:
\[
\forall X,V,\ell,p,\quad
(\forall u\in V,\exists a\in\mathbb R,\ s_u(N)\to a)
\Rightarrow
[\operatorname{limit}(V,\ell,p)\ \Longleftrightarrow\ \operatorname{upper}(V,\ell,p)].
\]
5. **Constants/normalization.** The same r/N occurs in hypothesis and both properties; no common a for different comparators required.
6. **Information/probability.** Separates existence of a limit from its nonpositive sign, without a stochastic theorem.
7. **Boundary.** Cannot drop the comparatorwise finite-limit premise. Empty V is vacuous. Divergence to minus infinity does not satisfy this premise even if upper holds.

## B004

1. **Objects.** Specific context f,h, constant-zero predictions, arbitrary N:N and u:R.
2. **Quantifier.** Every natural N and EVERY real u, not just [0,1].
3. **Assumptions.** None.
4. **Conclusion.** The concrete cumulative comparison has the exact telescoping value
\[
\forall N\in\mathbb N,\forall u\in\mathbb R,\quad
r(f,0,u,N)=-h_Nu.
\]
Played loss is zero; comparator loss telescopes to h_Nu because h_0=0.
5. **Constants/normalization.** This is unnormalized regret, with minus sign before h_Nu. No division by N yet.
6. **Information/probability.** Explicit deterministic losses and constant predictions; no future-dependent rule or probabilistic construction needed.
7. **Boundary.** N=0 gives zero; odd N gives zero; positive even N gives −Nu. Negative u is allowed in this identity and can give positive regret.

## B005

1. **Objects.** Fixed comparator set [0,1], concrete losses f and constant-zero prediction.
2. **Quantifier.** Closed target whose upper expands to every u in [0,1], every epsilon>0, and eventual natural N.
3. **Assumptions.** No external assumptions; membership and positive epsilon are conditional quantifiers inside upper.
4. **Conclusion.**
\[
\operatorname{upper}([0,1],f,0),\quad\text{i.e.}\quad
\forall u\in[0,1],\forall\varepsilon>0,\ \exists K,\forall N\ge K,\ 
r(f,0,u,N)/N\le\varepsilon.
\]
For positive N, the ratio is −u on even N and 0 on odd N.
5. **Constants/normalization.** Fixed interval endpoints 0,1; signed average, not absolute average.
6. **Information/probability.** Deterministic oscillatory sequence is compatible with a one-sided upper condition.
7. **Boundary.** u=0 yields identically zero, but the set also contains nonzero u. This property alone does not imply any ordinary real limit; N=0 is harmless totalized zero.

## B006

1. **Objects.** Concrete f, zero prediction, comparator exactly u=1 and positive-even horizons.
2. **Quantifier.** EVERY n:N.
3. **Assumptions.** None.
4. **Conclusion.** Along the explicitly positive even subsequence the normalized value is exactly minus one:
\[
\forall n\in\mathbb N,\quad
\frac{r(f,0,1,2(n+1))}{(2(n+1):\mathbb R)}=-1.
\]
5. **Constants/normalization.** Horizons are 2,4,6,..., not 0,2,4,...; denominator is the REAL coercion of exactly the same natural horizon.
6. **Information/probability.** Deterministic subsequence evaluation; no random parity selection.
7. **Boundary.** n=0 gives horizon 2 and a nonzero denominator. u=1 is an actual nondegenerate comparator inside [0,1]; this is not an artifact of division by zero or an empty comparator set.

## B007

1. **Objects.** Same concrete setup and comparator u=1; positive odd horizons.
2. **Quantifier.** Every n:N.
3. **Assumptions.** None.
4. **Conclusion.**
\[
\forall n\in\mathbb N,\quad
\frac{r(f,0,1,2n+1)}{(2n+1:\mathbb R)}=0.
\]
The positive odd subsequence has constant normalized value zero.
5. **Constants/normalization.** Horizons 1,3,5,...; exact same horizon in numerator and real denominator.
6. **Information/probability.** A second deterministic subsequence, to be distinguished from the even one.
7. **Boundary.** n=0 gives horizon 1, not zero. Both odd and even subsequences go to infinity; their distinct values are not finite-prefix anomalies.

## B008

1. **Objects.** Fixed f, zero predictions, comparator u=1; possible real limits a.
2. **Quantifier.** Closed negated existential over all a:R.
3. **Assumptions.** None.
4. **Conclusion.** No ordinary real limit exists:
\[
\neg\exists a\in\mathbb R,\quad
\left(N\mapsto r(f,0,1,N)/N\right)\longrightarrow a.
\]
5. **Constants/normalization.** Same normalized quantity as B006/B007; their subsequence values −1 and 0 are distinct.
6. **Information/probability.** Deterministic nonconvergence, not a failure of convergence in probability or expectation.
7. **Boundary.** The target negates existence of ANY real limit, not only a limit of zero. u=1 is feasible and nondegenerate. Does not negate the one-sided upper condition.

## B009

1. **Objects.** Fixed interval [0,1], f and constant-zero predictions.
2. **Quantifier.** Closed conjunction, with comparatorwise quantifiers inside upper and limit.
3. **Assumptions.** None.
4. **Conclusion.**
\[
\operatorname{upper}([0,1],f,0)\ \land\
\neg\operatorname{limit}([0,1],f,0).
\]
Thus the weaker upper property can hold while the finite nonpositive-limit property fails.
5. **Constants/normalization.** Same domain, losses, predictions and normalization in both conjuncts; this is not a comparison across different examples.
6. **Information/probability.** A deterministic separation witness. The feasible comparator u=1 suffices to obstruct a property requiring convergence for every comparator.
7. **Boundary.** Does not say all comparators fail to converge: u=0 has constant zero average. Does not claim upper is false or that any bounded-data assumption was met; none was imposed on the general loss family.

## B010

1. **Objects.** Total real target stream y, concrete q(y), squared-loss functions \(\ell_t(x)=(x-y_t)^2\), comparator set [0,1].
2. **Quantifier.** For EVERY y, assume all y_t lie in [0,1]; then every u in [0,1], every epsilon>0, eventual N in the expanded upper conclusion.
3. **Assumptions.** \(\forall t\in\mathbb N,\ y_t\in[0,1]\). This bounds the entire stream, not just one fixed prefix.
4. **Conclusion.**
\[
\forall y,\quad(\forall t,y_t\in[0,1])\Rightarrow
\forall u\in[0,1],\forall\varepsilon>0,\ \exists K,\forall N\ge K,\quad
\frac{\sum_{t<N}(q_t(y)-y_t)^2-\sum_{t<N}(u-y_t)^2}{N}\le\varepsilon.
\]
5. **Constants/normalization.** Initialization 1/2, later prediction is the strict-prefix mean with denominator t. The conclusion has no explicit numerical convergence rate.
6. **Information/probability.** Actual q formula identifies the mathematical predictor and its strict-past inputs; no named external algorithm identity is supplied. Same target stream drives the predictor and both loss sums. No stochastic assumptions.
7. **Boundary.** Endpoints allowed. This asserts upper, not ordinary convergence, a zero limit, or an absolute-value rate. N=0 is immaterial to eventuality; q_0 remains 1/2 rather than empty mean zero.

## B011

1. **Objects.** Arbitrary X,V,ell,p and real bound \(\beta:X\to\mathbb N\to\mathbb R\).
2. **Quantifier.** Every X,V,ell,p,beta; first eventual upper comparison for every u∈V, then convergence of beta(u,·) to zero for every u∈V; conclusion upper.
3. **Assumptions.**
\[
\forall u\in V,\ \forall^{\mathrm{eventually}}N,\quad s_u(N)\le\beta(u,N),
\qquad
\forall u\in V,\quad\beta(u,N)\to0.
\]
Neither hypothesis gives a uniform threshold over all u; no nonnegativity condition on beta is required.
4. **Conclusion.**
\[
\forall X,V,\ell,p,\beta,\quad
[(\forall u\in V,\ \forall^{\mathrm{eventually}}N,\ s_u(N)\le\beta(u,N))
\land(\forall u\in V,\ \beta(u,N)\to0)]
\Rightarrow\operatorname{upper}(V,\ell,p).
\]
5. **Constants/normalization.** Limit of the upper-bound sequence is exactly zero; regret is divided by N once. No lower comparison or rate.
6. **Information/probability.** Deterministic scalar limiting-bound argument for arbitrary supplied predictions, not an algorithm construction or probability bound.
7. **Boundary.** Does not ensure s_u converges; an oscillating or unbounded-below s_u can still be upper-bounded. V empty is vacuous and finite exceptional N are permitted.

## B012

1. **Objects.** Any X:Type v, real losses ell, predictions p, comparator u:X, natural N.
2. **Quantifier.** Universal over all these objects without a comparator set.
3. **Assumptions.** None beyond the types.
4. **Conclusion.** The comparator difference can be expressed as a sum of roundwise differences:
\[
\forall X,\ell,p,u,N,\quad
r(\ell,p,u,N)=\sum_{t=0}^{N-1}\bigl(\ell_t(p_t)-\ell_t(u)\bigr).
\]
5. **Constants/normalization.** No division in this identity; same N terms and fixed u throughout.
6. **Information/probability.** Finite real-sum algebra only. Does not establish causality or identify any particular algorithm.
7. **Boundary.** N=0 both sides zero; no sign, boundedness, nonempty comparator set or probability premise.

## Ambiguities and scope

No ambiguity in the supplied definitions blocks reconstruction. The important limitations are explicit: arbitrary p has no algorithmic identity or causal law; q is a concrete prefix formula but not an externally attributed algorithm; upper is a one-sided eventual condition, whereas limit asserts existence of an ordinary finite real limit at a nonpositive value. The positive-even and positive-odd subsequences at feasible u=1 provide a nondegenerate separation, unrelated to N=0 totalization. All these are typed proposition descriptions. Source, proof, compilation and acceptance are not assessed.

