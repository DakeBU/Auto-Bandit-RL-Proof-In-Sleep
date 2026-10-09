# General-initialization draft reconstruction v3

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, without independently attested runtime model or effort. This reused automated actor retains earlier staged decoder/project history. No absolute blindness, human review or external independence is claimed. Only the designated v3 packet, index, two indexed files and the own four-target v2 report/receipt were read. Earlier fifty-target artifacts were neither read nor modified; four-target v2 outputs remain unchanged. The four supplied headers are proposed target types: their text is not proof, compilation, source-correspondence or chapter-acceptance evidence.

## Six exact context definitions

1. For arbitrary action type X, real loss family ℓ, supplied trace q, comparator u and natural horizon T,
\[
R_T(\ell,q,u)=\sum_{t<T}\ell_t(q_t)-\sum_{t<T}\ell_t(u).
\]
This signed comparator regret definition alone imposes no feasibility or causality.

2. The exact `NoRegret` predicate is the eventual upper condition
\[
\forall u\in V\ \forall\epsilon\in\mathbb R,\quad\epsilon>0\Rightarrow
\exists N\in\mathbb N\ \forall T\ge N,\quad R_T(\ell,q,u)/T\le\epsilon.
\]
The threshold may depend on u and ε. It is neither absolute-value convergence nor a requirement that each fixed-comparator ratio have an ordinary real limit.

3. For any real observation sequence y, \(e_T(y)=\sum_{t<T}y_t/T\). Finite range T means indices 0,...,T-1. The denominator is real-coerced T, and totalized division gives e0=0.

4. The half-initialized predictor is \(p_0(y)=1/2\), \(p_t(y)=e_t(y)\) for t>0.

5. The general-initialized actual predictor is \(p^a_0(y)=a\), \(p^a_t(y)=e_t(y)\) for t>0. Thus changing a affects only the first prediction: the supplied empirical-mean definition does not recursively feed a into future averages. At each t>0 the rule reads exactly observations i<t; current and future observations are excluded. a and y specify one infinite prediction sequence before a horizon is selected.

6. The squared best-regret metric is
\[
G_T(y,q)=\sum_{t<T}(q_t-y_t)^2-
\inf\left\{\sum_{t<T}(u-y_t)^2:u\in[0,1]\right\}.
\]
The infimum is the real `sInf` of the feasible constant-comparator loss image. It is over the entire interval, not a supplied arbitrary comparator or a time-varying comparator sequence. There is no expectation: this is realized-prefix best-comparator regret. Although this metric refers to the true feasible optimum value, the bare definition itself is not a separate theorem of attainment or uniqueness. At T0 the comparator-loss image is {0}, all prediction loss sums vanish, and G0=0 for every q. Normalized G0/0=0 under totalized division. The initial prediction a differs from the empty empirical mean0 unless a=0.

This is a new versioned finite target: G002 now uses the exact reciprocal sum below instead of the v2 logarithmic conclusion. G001, G003 and G004 retain their mathematical scopes and are fully restated here. This is not a silent correction of old inputs or proof evidence.

For the targets below abbreviate \(G_T^a=G_T(y,p^a(y))\) and \(G_T^{1/2}=G_T(y,p(y))\). These always use the same observation stream and the indicated actual predictor; no arbitrary supplied prediction trace is substituted.

## G001 — exact first-loss correction for arbitrary real initialization

For every real initial value, every real observation stream and every positive horizon, best regret of the general predictor equals best regret of the half-initialized predictor plus the difference of their first squared losses:
\[
\forall a\in\mathbb R\ \forall y:\mathbb N\to\mathbb R\ \forall T\in\mathbb N,\quad
0<T\Rightarrow
G_T^a=G_T^{1/2}+\left((a-y_0)^2-(1/2-y_0)^2\right).
\]

1. **Objects/spaces:** arbitrary real a, real stream y, positive natural horizon, two explicit prediction rules and the same feasible-best comparator-loss infimum.
2. **Quantifiers/order:** initial a, y, T, then the proof T>0; no bound or future limit parameter is introduced.
3. **Assumptions:** only T>0. Neither a nor y is required to lie in [0,1]. Both predictors and metrics remain defined even when their values are infeasible.
4. **Conclusion/metric:** exact equality of true feasible-best regret values with a signed first-loss correction. The first term in that correction is the general initial loss and the subtracted term is the half-initial loss; the correction need not be nonnegative.
5. **Constants/indices/empty horizon:** initial constant1/2, observation index0, positive T guarantees this loss is scored. At T0 both best regrets are zero but the displayed correction need not vanish, so the positive-horizon premise is material. If a=1/2 the correction is zero.
6. **Information/probability:** deterministic same-stream comparison. For t>0 both actual predictors are the same strict-past empirical mean. No stochastic averaging, random initialization or hindsight observation used to choose a is asserted.
7. **Boundaries:** not a bound, rate or feasibility theorem. It is not a statement about arbitrary q, nor about a modified recurrence that retains a in future means. It does not claim G001 already has a proof or an accepted source counterpart.

## G002 — positive-horizon exact reciprocal-sum upper bound

For every feasible initialization and every feasible scored observation prefix, the same actual general-initialized predictor has cumulative best regret bounded by one plus a finite reciprocal sum:
\[
\forall a\in\mathbb R\ \forall y:\mathbb N\to\mathbb R\ \forall T\in\mathbb N,\quad
0<T\Rightarrow a\in[0,1]\Rightarrow
(\forall t<T,y_t\in[0,1])\Rightarrow
G_T^a\le 1+\sum_{t\in\operatorname{range}(T-1)}\frac{4}{(t:\mathbb R)+2}.
\]
For positive T, the right side is equivalently \(1+\sum_{j=2}^{T}4/j\), empty at T=1. Exact refers to the expression specified in this upper bound; the conclusion is an inequality, not equality of regret to that expression.

1. **Objects/spaces:** fixed real initial a, real stream y, positive natural horizon, actual predictor p^a and realized feasible-best regret. Its benchmark is the infimum over all fixed u in [0,1], not one arbitrary supplied comparator.
2. **Quantifiers/order:** a, y, T, positivity, initial feasibility, prefix support. The same actual predictor defined from a and y is used, with no supplied substitute trace or horizon-specific learner.
3. **Assumptions:** a in [0,1] and y_t in [0,1] only for t<T. Future observations are unrestricted. No causal-performance premise, supplied regret bound, mean convergence or probability assumption occurs; actual prediction behavior is given by definition.
4. **Conclusion/metric:** one-sided cumulative true-best regret upper bound, additive constant1 and the displayed finite sum. It is not absolute regret, equality, or just a comparison against one fixed u.
5. **Constants/indices/empty horizon:** T-1 is natural subtraction. For positive T, indices t=0,...,T-2 give denominators2,...,T and T-1 terms. Numerator4 and constant1 are exact, not1/4 or5. At T1 the bound is1; at T2 it is3. T0 is excluded by the type although G0 and the bound expression are total. No logarithm occurs in this v3 conclusion.
6. **Information/probability:** one deterministic actual strict-past process: initial prediction a, later empirical means. Comparator optimization uses the whole scored prefix while the played value excludes the current observation. No expectation or seed is involved.
7. **Boundaries:** infeasible initial values are outside this bound even though G001 permits them. No sharpness, lower bound, ordinary fixed-comparator limit or exact regret value is claimed. The old logarithmic v2 target is not silently substituted or proved.

## G003 — comparatorwise eventual upper no-regret

For every feasible initialization and every pointwise feasible infinite stream, the actual general predictor satisfies the exact one-sided epsilon upper condition against every feasible constant comparator:
\[
\begin{gathered}
\forall a\in\mathbb R\ \forall y:\mathbb N\to\mathbb R,\quad
a\in[0,1]\Rightarrow(\forall t\in\mathbb N,y_t\in[0,1])\Rightarrow\\
\forall u\in[0,1]\ \forall\epsilon\in\mathbb R,\quad
0<\epsilon\Rightarrow\exists N\in\mathbb N\ \forall T\ge N,\quad
\frac{\sum_{t<T}(p^a_t(y)-y_t)^2-\sum_{t<T}(u-y_t)^2}{T}\le\epsilon.
\end{gathered}
\]

1. **Objects/spaces:** feasible real initial value, pointwise feasible deterministic infinite stream, actual p^a, squared loss, feasible fixed real comparators and natural horizons.
2. **Quantifiers/order:** a, y, initial feasibility, all-time support, then expansion of NoRegret: u/membership, ε/positivity, eventual threshold N, every T≥N. a and the algorithm are fixed before all horizons; N may depend on a,y,u,ε.
3. **Assumptions:** initial feasibility and every-time observation feasibility. No empirical-mean convergence or ordinary fixed-regret convergence premise is supplied.
4. **Conclusion/metric:** upper no-regret for signed comparator regret. It does not state existence of any ordinary real limit, zero limit, or absolute sublinearity for each comparator.
5. **Constants/indices/empty horizon:** interval endpoints0,1, arbitrary positive ε; totalized ratio at T0 is0, and the eventual tail can ignore this finite initial value. No fixed uniform threshold or rate constant appears.
6. **Information/probability:** deterministic all-time statement for one actual initialized strict-past predictor. u is a fixed comparator across times; no stochastic measure or average over runs.
7. **Boundaries:** not a uniform-in-u eventual bound, not the stronger ordinary-limit predicate, not an arbitrary-trace guarantee and not a statement for infeasible a. Best-regret convergence is a separate target, G004.

## G004 — ordinary zero limit of normalized true-best regret

For every feasible initialization and pointwise feasible infinite stream, normalized feasible-best regret of the same actual predictor converges to zero:
\[
\forall a\in\mathbb R\ \forall y:\mathbb N\to\mathbb R,\quad
a\in[0,1]\Rightarrow(\forall t\in\mathbb N,y_t\in[0,1])\Rightarrow
\lim_{T\to\infty}\frac{G_T(y,p^a(y))}{T}=0.
\]

1. **Objects/spaces:** initial a, infinite real stream, actual predictor p^a, feasible constant-comparator infimum and the real normalized best-regret sequence.
2. **Quantifiers/order:** a, y, initial feasibility and all-time support; T varies inside the function supplied to Tendsto. No horizon-specific initialization or new predictor is chosen.
3. **Assumptions:** exactly feasible a and pointwise feasible y at all natural times. No empirical-mean convergence, stochastic independence or law is required by the target.
4. **Conclusion/metric:** an actual ordinary real limit at natural `atTop` to `nhds 0` of normalized true-best regret. This is not merely a limsup bound or equivalence between conditions, and the metric is not normalized regret to one arbitrary fixed comparator.
5. **Constants/indices/empty horizon:** limit exactly0, real denominator T, cumulative sums over t<T. At T0 G0/0=0 by total division; that initial value does not determine the limit. The initial value a remains fixed throughout.
6. **Information/probability:** deterministic same-run before-reveal predictions; the optimal comparison value uses all T realized observations. No infimum/expectation interchange occurs because no expectation is present.
7. **Boundaries:** does not assert ordinary limits of all fixed-comparator regret ratios, empirical-mean convergence, a finite-time rate beyond other targets, or results for arbitrary supplied traces. It is a proposed convergence conclusion, not existing proof evidence.

## Completeness and remaining context

All four targets have complete prose, LaTeX and seven-slot reconstructions using the six supplied definitions. No missing context or blocking semantic ambiguity was identified. G001 permits arbitrary real initialization and observations but requires positive horizon; G002 additionally uses feasible initialization and finite-prefix support with the v3 bound 1 plus the sum over range(T-1); G003/G004 require feasible initialization and all-time support. G003's comparatorwise eventual upper condition remains distinct from G004's ordinary zero limit of normalized best regret. No truth, implementation, proof, compilation, source correspondence or chapter acceptance is inferred, and no old fifty-target artifact is superseded.
