# Statement-only reconstruction

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, with runtime model and effort unverified. This automated decoder has reused staged history and may retain prior background; no absolute blindness, external independence or human review is claimed. Only the designated packet and neutral context/statements were read. The five displayed theorem types are reconstructed below, not proved or checked for compilation. No source equivalence or acceptance is inferred from their syntax.

## Literal definitions and notation

For any real sequence y define
\[
\bar y_n=\frac{\sum_{t<n}y_t}{n},\qquad
p_t=\begin{cases}1/2,&t=0,\\\bar y_t,&t>0.\end{cases}
\]
The sum uses exactly indices 0,...,n-1. Natural denominators are coerced to reals. Lean's totalized division gives \(\bar y_0=0\), while \(p_0=1/2\). The actual prediction p uses only strict-past observations; its value at time t does not use y_t. No probability space, stochastic seed or independence assumption occurs anywhere in this packet.

For an arbitrary type X, real losses \(\ell_t:X\to\mathbb R\), a supplied action sequence q and fixed comparator u, the comparator regret is
\[
R_T(\ell,q,u)=\sum_{t<T}\ell_t(q_t)-\sum_{t<T}\ell_t(u).
\]
For squared losses and the specified p write \(R_T(u)=\sum_{t<T}(p_t-y_t)^2-\sum_{t<T}(u-y_t)^2\). The comparator may be specified as \(u=\bar y_T\) at a given horizon, but a fixed-u limit uses a single u as T varies.

The separate best-regret definition is
\[
G_T(y,q)=\sum_{t<T}(q_t-y_t)^2-
\inf\left\{\sum_{t<T}(u-y_t)^2:u\in[0,1]\right\}.
\]
This real `sInf` is over the continuous feasible interval of constant comparators for this realized deterministic prefix. There is no expectation, and no interchange of minimization and expectation is relevant here. The definition alone does not assert attainment or uniqueness. At T0 all loss sums vanish, the comparator-loss image is {0}, and both comparator regret and best regret are zero. Their normalized values at zero are also zero by totalized division.

The exact predicate `LimitNoRegret` is
\[
\forall u\in V,\ \exists a\in\mathbb R,\quad a\le0\ \land\
\lim_{T\to\infty}\frac{R_T(\ell,q,u)}{T}=a.
\]
The limit is an ordinary real limit along natural T (`atTop` to `nhds a`), not merely a limsup upper bound. The limit value may depend on u. This predicate neither requires a common limit for all comparators nor itself adds feasibility of the prediction sequence. Definitions are total; finite zero-index values do not control their eventual limits.

## 1. meanPredict_bestLoss_nonneg

For every real observation sequence and horizon, the actual mean predictor's cumulative squared loss is at least the cumulative loss of the constant empirical mean of that horizon:
\[
\forall y:\mathbb N\to\mathbb R\ \forall T\in\mathbb N,
\qquad 0\le R_T(\bar y_T).
\]

1. **Objects/spaces:** an arbitrary deterministic real sequence, its strict-past prediction rule, horizon-T empirical mean and finite squared losses.
2. **Quantifiers/order:** y then T; the comparator \(\bar y_T\) is determined by these arguments rather than universally fixed across horizons.
3. **Assumptions:** no range bound on y, no positive-T premise, no convergence assumption.
4. **Conclusion/metric:** nonnegativity of signed regret against the horizon empirical mean. It is not the separately defined feasible best-regret expression in the statement.
5. **Constants/indices/T0:** p0=1/2; both finite sums range over t<T. At zero, comparator is \(\bar y_0=0\) and the conclusion is 0≤0.
6. **Probability/information:** deterministic. Predictions are strict-past, while the comparison mean uses all T observations and is a hindsight constant for that prefix.
7. **Boundaries:** the mean need not lie in [0,1] for arbitrary y. No feasible-domain constraint, upper bound, uniqueness or optimizer-existence theorem is stated. The conclusion applies to this specific prediction rule, not arbitrary prediction sequences.

## 2. meanPredict_comparator_decomposition

For every sequence, every fixed real comparator and every horizon, squared-loss regret equals regret to the empirical mean minus the horizon-weighted squared distance from that mean:
\[
\forall y:\mathbb N\to\mathbb R\ \forall u\in\mathbb R\ \forall T\in\mathbb N,
\qquad R_T(u)=R_T(\bar y_T)-T(u-\bar y_T)^2.
\]

1. **Objects/spaces:** deterministic sequence y, actual p, arbitrary real u, horizon and its empirical mean.
2. **Quantifiers/order:** y, then u, then T. u is not restricted to the interval and is distinct from the horizon-dependent empirical-mean comparator.
3. **Assumptions:** no boundedness, feasibility, positivity or convergence premises.
4. **Conclusion/metric:** exact signed decomposition with a minus sign before \(T(u-\bar y_T)^2\).
5. **Constants/indices/T0:** real factor T, exponent 2, t<T finite losses. At T0 both regrets are zero and the correction is 0, despite arbitrary u.
6. **Probability/information:** no probability; the hindsight comparator is used only for comparison, not as the current play. p remains the same strict-past process on both sides.
7. **Boundaries:** fixed-comparator regret may be negative. The identity does not assert nonnegativity for every u or a loss/convergence rate; reversing the correction sign changes the meaning.

## 3. meanPredict_bestRegret_average_tendsto_zero

For any sequence whose every observation is in [0,1], the average feasible best-comparator regret of the actual mean predictor tends to zero:
\[
\forall y:\mathbb N\to\mathbb R,\quad
[\forall t\in\mathbb N,\ y_t\in[0,1]]\Longrightarrow
\lim_{T\to\infty}\frac{G_T(y,p)}{T}=0.
\]

1. **Objects/spaces:** deterministic pointwise-bounded sequence, actual p, infimum of finite cumulative comparator losses on [0,1] and real normalized regret.
2. **Quantifiers/order:** y then its all-time support premise; T varies inside the function whose natural-index limit is taken.
3. **Assumptions:** every y_t is feasible, pointwise for all natural times; no empirical-mean convergence or stochastic iid premise.
4. **Conclusion/metric:** actual ordinary real convergence of normalized G_T to zero, not just equivalence to another condition or an eventual upper condition.
5. **Constants/indices/T0:** feasible comparator interval [0,1], division by real T, limit exactly 0. G0/0=0, a finite initial value irrelevant to the limit.
6. **Probability/information:** this is pathwise deterministic evaluation on a supplied sequence, with no expectation. The comparator infimum uses the entire realized finite prefix while p uses only strict history.
7. **Boundaries:** this alone is not an assertion that each normalized fixed-u regret has an ordinary limit. Nor does the statement supply a numerical finite-time bound or rate. It does not assume the empirical mean converges.

## 4. meanPredict_fixedRegret_limit_iff

For bounded observations, any fixed real comparator u and any real candidate limit a, its normalized regret converges to a exactly when the squared distance between u and the horizon empirical mean converges to -a:
\[
\forall y:\mathbb N\to\mathbb R,\quad
[\forall t,y_t\in[0,1]]\Longrightarrow
\forall u,a\in\mathbb R,\quad
\left[\lim_{T\to\infty}\frac{R_T(u)}{T}=a\right]
\Longleftrightarrow
\left[\lim_{T\to\infty}(u-\bar y_T)^2=-a\right].
\]

1. **Objects/spaces:** pointwise bounded deterministic y, fixed arbitrary real u, candidate real a, two real sequences indexed by horizons.
2. **Quantifiers/order:** y, all-time support proof, u then a; the biconditional is after both fixed parameters.
3. **Assumptions:** only the support premise; neither mean convergence nor a≤0 is assumed, and u need not belong to [0,1].
4. **Conclusion/metric:** equivalence of two ordinary limit statements, not independent existence of either limit. The right target is negative a, not a.
5. **Constants/indices/T0:** square exponent 2; at zero the regret quotient is 0 but the squared-distance value is u² because \(\bar y_0=0\). Pointwise equality at T0 is not claimed or needed for the limit equivalence.
6. **Probability/information:** both quantities arise from the same fixed deterministic sequence and same comparator. No expectation or random-law qualification.
7. **Boundaries:** nonnegativity of squared distances constrains any actual finite limit -a to be nonnegative, but the header does not pre-restrict a. Convergence of distance squared from one u is not stated as equivalent to convergence of the empirical mean itself. No universal convergence claim for arbitrary bounded y is added.

## 5. meanPredict_limitNoRegret_of_mean_converges

If observations are always feasible and their empirical means converge to m, every fixed real comparator has normalized regret limit \(-(u-m)^2\), and the exact ordinary-limit no-regret predicate holds on [0,1]:
\[
\begin{gathered}
\forall y:\mathbb N\to\mathbb R,\quad
[\forall t,y_t\in[0,1]]\Longrightarrow\forall m\in\mathbb R,\quad
[\bar y_T\longrightarrow m]\Longrightarrow\\
\left[\forall u\in\mathbb R,\quad\frac{R_T(u)}{T}\longrightarrow-(u-m)^2\right]
\ \land\
\left[\forall u\in[0,1],\ \exists a\in\mathbb R,
\ a\le0\ \land\ \frac{R_T(u)}{T}\longrightarrow a\right].
\end{gathered}
\]
Every arrow to a limit here means \(T\to\infty\) along natural horizons. The second conjunct is the expansion of the exact supplied `LimitNoRegret` predicate for squared loss and p.

1. **Objects/spaces:** bounded deterministic y, its strict-past predictor and empirical-mean sequence, supplied candidate mean limit m, and all real fixed comparators.
2. **Quantifiers/order:** y, all-time support, m, convergence proof for the empirical mean, then a conjunction. In the first conjunct u ranges over all reals; in the second, each feasible u precedes its own existential limit a.
3. **Assumptions:** both pointwise boundedness and ordinary empirical-mean convergence are required. No explicit m∈[0,1] premise or probabilistic assumptions are present; an interval constraint on m can follow from the given data but must not be added as a new hypothesis.
4. **Conclusion/metric:** actual convergence statements for each real u to an explicit nonpositive value, together with ordinary-limit no-regret on the feasible interval. This is a sufficient-condition result rather than an equivalence or a universal assertion for all bounded y without mean convergence.
5. **Constants/indices/T0:** limit \(-(u-m)^2\), potentially strictly negative, not necessarily zero. At u=m it is zero. Real division by T is total at zero; that initial quotient has no effect on the conclusion.
6. **Probability/information:** m is used to describe the limit and is not an input to p. The prediction rule remains the actual initial-half strict-past empirical mean, with no oracle mean access.
7. **Boundaries:** the no-regret witness may depend on u; it is not one common a across comparators. No assertion of zero fixed-comparator limits for all u, stochastic convergence, finite-time rate or necessity of empirical-mean convergence is included.

## Ambiguity and evidence boundary

No blocking semantic ambiguity was found. The two different metrics are kept separate: comparator regret at a specified u and feasible best-regret using a real infimum. Their signed decompositions and ordinary-limit scopes differ. The packet supplies target theorem headers, not proof bodies or compile evidence, and none was sought. This report is neutral semantic reconstruction only; no proof, source, compilation or acceptance verdict is issued.
