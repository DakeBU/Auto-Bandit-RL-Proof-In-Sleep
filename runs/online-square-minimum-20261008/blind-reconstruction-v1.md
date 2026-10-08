# Neutral reconstruction: C0-C3 and Q001-Q006

Actor /root/osd_blind. Requested GPT-6 Astra / medium, without escalation. Runtime model and effort are not independently attested. This reused actor has earlier staged neutral-decoder history covering current-support/policy, scalar losses, linearization, scalar tuning, unit scaling, foundations, finite-prefix/state/domain, lower-bound and one-sided-limit interfaces. Inherited background may exist; this is not an absolute-blind, first-exposure, human or external review.

For this task only the designated neutral-packet-v1.md, neutral-inputs-v1.json, and its sole neutral-context-v1.lean row were read. No other source, contract, public name, map, target proof, or existing review was consulted. The context file repeats the supplied four definitions and six closed Prop descriptions. Claimed type compilation is not independently verified here. Closed Prop definitions do not provide proofs of those propositions. Source fidelity, proof validity and acceptance are not assessed.

Let \(I=[0,1]\), \(L_T(y,u)=\sum_{t=0}^{T-1}(u-y_t)^2\), and \(S_T(y,p)=\sum_{t=0}^{T-1}(p_t-y_t)^2\). All sequences are total maps from natural numbers to real numbers. Natural counts are coerced to real for division and logarithms; Finset.range T is exactly 0,...,T-1. Total real division gives 0/0=0. The image set \(L_T(y,\cdot)''I\) consists of scalar loss VALUES, not comparator points. It is generally an infinite set despite the finite horizon. No probability model, expectation, filtration or independent-data premise is supplied.

Every definition and proposition below is decoded independently through seven slots: objects; quantifier order; assumptions; conclusion/defining equation; constants and indices; information/probability; boundaries.

## C0

1. **Objects.** Real target sequence y and natural count T; output is real.
2. **Quantifier order.** Defined for every y:N→R and every T:N.
3. **Assumptions.** None; no positivity or interval restriction.
4. **Defining equation.** The totalized prefix arithmetic mean is
\[
\forall y,T,\qquad C0(y,T)=\frac{\sum_{t=0}^{T-1}y_t}{T}.
\]
5. **Constants and indices.** T summands, denominator the same real-coerced T; no initial pseudocount.
6. **Information/probability.** For positive T it uses all targets in the finite prefix, including index T-1, but none at index T or later. It is a deterministic finite arithmetic expression.
7. **Boundaries.** At T=0 the sum is empty and C0(y,0)=0 by total real division. This convention is not the initial predictor C1(y,0)=1/2. For unbounded targets C0 need not be in I.

## C1

1. **Objects.** Real target sequence y and natural time t; real prediction.
2. **Quantifier order.** Defined for every y and t.
3. **Assumptions.** None.
4. **Defining equation.** The explicit predictor uses a fixed midpoint initially and the strict-prefix mean afterward:
\[
\forall y,t,\qquad C1(y,t)=
\begin{cases}
1/2,&t=0,\\
C0(y,t),&t>0.
\end{cases}
\]
5. **Constants and indices.** At positive t the denominator is t and the inputs are y_0,...,y_{t-1}. Current y_t is excluded.
6. **Information/probability.** This is an actually specified deterministic predictor, rather than an arbitrary supplied trace. Its displayed formula shows strict-past input dependence; no external algorithm identity or probability law is supplied.
7. **Boundaries.** The t=0 branch avoids replacing the midpoint with the empty mean. Feasibility in I for positive t requires appropriate past-target bounds; none is built into the definition itself. No computational implementation is asserted by a noncomputable mathematical definition.

## C2

1. **Objects.** Real losses ell:N→R→R, arbitrary supplied prediction sequence p:N→R, fixed real comparator u, natural T.
2. **Quantifier order.** Defined for every ell,p,u,T.
3. **Assumptions.** None: p and u need not lie in I, and p has no causality premise.
4. **Defining equation.** Signed cumulative excess against one fixed comparator is
\[
\forall\ell,p,u,T,\qquad
C2(\ell,p,u,T)=\sum_{t<T}\ell_t(p_t)-\sum_{t<T}\ell_t(u).
\]
5. **Constants and indices.** Both sums use the same T played indices; no division by T, absolute value, or minimization.
6. **Information/probability.** The supplied trace may depend on any external information; this definition does not produce it. The comparator affects evaluation only. No expectation appears.
7. **Boundaries.** T=0 yields zero. Negative excess is permitted. Real losses are finite at each input, with no EReal fallback issue.

## C3

1. **Objects.** Real target stream y, arbitrary real prediction trace p, natural T; comparator set I.
2. **Quantifier order.** Defined for every y,p,T without feasibility assumptions.
3. **Assumptions.** None in the definition.
4. **Defining equation.** The signed excess over the infimum fixed-comparator squared loss is
\[
\forall y,p,T,\qquad
C3(y,p,T)=S_T(y,p)-\inf\{L_T(y,u):u\in I\},
\]
where the formal operation is real sInf of that image set.
5. **Constants and indices.** Same finite T-term squared-loss sums. It is an infimum of values over the full interval, not a minimum over finitely many sampled comparators and not an infimum over times.
6. **Information/probability.** The comparator optimization uses the full played prefix in hindsight. Predictions remain the SAME supplied p; minimizing the comparator does not replace the prediction trace. No randomization.
7. **Boundaries.** The definition alone does not name a minimizing point. In this particular setting the value set is nonempty (u=0 is available) and bounded below by zero; it is not an empty-set or unbounded-below sInf fallback. At T=0 its value set is {0}, so C3=0. Even feasible time-varying predictions can outperform every fixed comparator, so this signed quantity need not be nonnegative.

## Q001

1. **Objects.** Target sequence y, natural horizon T, prefix mean C0(y,T), feasible comparator u∈I.
2. **Quantifier order.** For every y and T, assume all targets t<T feasible; conclude mean feasibility AND then a comparison for EVERY feasible u.
3. **Assumptions.** \(\forall t<T,\ y_t\in I\). No T>0 condition.
4. **Conclusion.** The named mean is a feasible attained minimum of the finite-horizon comparator objective:
\[
\forall y,T,\quad(\forall t<T,y_t\in I)\Rightarrow
\left[C0(y,T)\in I\ \land\
\forall u\in I,\ L_T(y,C0(y,T))\le L_T(y,u)\right].
\]
5. **Constants and indices.** Objective is a sum of T squared deviations with no 1/2 coefficient. One fixed C0(y,T) appears in every comparator term.
6. **Information/probability.** This explicitly provides a minimizing point, stronger than merely saying an infimum exists. The point uses the entire target prefix; it is not asserted available to an earlier prediction.
7. **Boundaries.** T=0 is included: C0=0∈I and every comparator has loss zero. It does not claim uniqueness, particularly not at T=0. Endpoints allowed; targets at index T and later unrestricted.

## Q002

1. **Objects.** y,T, the image loss-value set \(L_T(y,\cdot)''I\), and the prefix mean.
2. **Quantifier order.** For every y,T, under prefix target feasibility.
3. **Assumptions.** \(\forall t<T,\ y_t\in I\), with no positive-horizon premise.
4. **Conclusion.** The real infimum equals the attained value at that mean:
\[
\forall y,T,\quad(\forall t<T,y_t\in I)\Rightarrow
\operatorname{sInf}\bigl(L_T(y,\cdot)''I\bigr)=L_T(y,C0(y,T)).
\]
5. **Constants and indices.** Exact equality of objective values, no approximation, averaging or residual.
6. **Information/probability.** Connects the infimum formulation with the explicit minimizing comparator. No choice of a new prediction sequence.
7. **Boundaries.** At T=0 both sides zero. “Finite horizon” does not make the interval image a finite set. No statement that the mean is the constrained minimizer for arbitrary unbounded targets is included; the target-feasibility assumption is retained.

## Q003

1. **Objects.** y and arbitrary prediction p:N→R, T:N, squared-loss stream ell_t(x)=(x−y_t)^2.
2. **Quantifier order.** Every y,p,T under target-prefix feasibility.
3. **Assumptions.** \(\forall t<T,\ y_t\in I\). NO feasibility, causality, or C1 identity required of p.
4. **Conclusion.** Infimum-comparator excess equals excess against the explicit mean using the same trace:
\[
\forall y,p,T,\quad(\forall t<T,y_t\in I)\Rightarrow
C3(y,p,T)=C2((t,x)\mapsto(x-y_t)^2,p,C0(y,T),T).
\]
5. **Constants and indices.** Same T, p, and target sequence on both sides; exact identity.
6. **Information/probability.** This is a comparator substitution, not a construction or identification of the prediction algorithm. The mean is hindsight; p is arbitrary.
7. **Boundaries.** T=0 both zero. Neither side must be nonnegative; the identity does not constrain p to the interval or to strict-past information.

## Q004

1. **Objects.** y,p,T and real feasible comparator u.
2. **Quantifier order.** For every y,p,T satisfying prefix feasibility, then every u∈I.
3. **Assumptions.** \(\forall t<T,y_t\in I\) and u∈I; no constraint on p.
4. **Conclusion.** Signed excess against any fixed feasible comparator is no greater than the excess against the infimum comparator:
\[
\forall y,p,T,u,\quad[(\forall t<T,y_t\in I)\land u\in I]\Rightarrow
C2((t,x)\mapsto(x-y_t)^2,p,u,T)\le C3(y,p,T).
\]
5. **Constants and indices.** Inequality direction is ≤: subtracting the smallest comparator loss yields the largest excess. No multiplicative penalty.
6. **Information/probability.** Comparator varies while the same supplied prediction trace stays fixed. No expectation or external policy assumption.
7. **Boundaries.** T=0 yields equality zero. The comparison is signed, not an absolute-value bound; negative values are allowed. u must be feasible even though p need not be.

## Q005

1. **Objects.** Target sequence y, POSITIVE natural T, explicitly defined predictor p=C1(y).
2. **Quantifier order.** Every y,T with T>0, then bounded played-prefix hypothesis, leading to the stated bound.
3. **Assumptions.** T>0 and \(\forall t<T,y_t\in I\).
4. **Conclusion.** The actual midpoint/prefix-mean predictor has the following finite-horizon excess over the best feasible fixed comparator value:
\[
\forall y,T,\quad[T>0\land(\forall t<T,y_t\in I)]
\Rightarrow C3(y,C1(y),T)\le4+4\log T.
\]
5. **Constants and indices.** Natural logarithm of real-coerced T; additive 4 and multiplier 4 exactly. No division of regret by T. Predictions at t=0,...,T-1 use strict prefixes.
6. **Information/probability.** Unlike Q003/Q004 this binds the actual predictor to C1. Comparator infimum still uses the whole horizon; no independent prediction trace can be substituted. No stochastic law.
7. **Boundaries.** T=0 is excluded even though C3 is defined there. At T=1 RHS=4. No all-comparator causality claim, lower bound, absolute-value regret estimate, or assertion of equality/sharpness is present.

## Q006

1. **Objects.** y, positive T, same actual C1 predictor and interval comparator objective.
2. **Quantifier order.** Every y,T with T>0 and every played target in I.
3. **Assumptions.** T>0; \(\forall t<T,y_t\in I\).
4. **Conclusion.** The initial one-quarter plus shifted reciprocal sum bounds the signed infimum-comparator excess:
\[
\forall y,T,\quad[T>0\land(\forall t<T,y_t\in I)]
\Rightarrow
C3(y,C1(y),T)\le\frac14+
\sum_{j\in\operatorname{range}(T-1)}\frac4{(j:\mathbb R)+2}.
\]
5. **Constants and indices.** Natural subtraction T−1 gives T−1 remainder terms for positive T. Their real denominators are 2,...,T; no denominator 1. Initial 1/4 is separate, numerator 4 remains in each later term.
6. **Information/probability.** The fixed initialization is 1/2, followed by actual strict-prefix means. This bound is not supplied for an arbitrary p or arbitrary initial point. No probability or normalization by T.
7. **Boundaries.** At T=1 the remainder range is empty, so RHS=1/4. T=0 excluded. The inequality does not assert the later coefficients or bound are attained, nor nonnegativity of C3. Targets beyond the played prefix remain unrestricted.

## Ambiguities, signed comparison and evidence boundary

No ambiguity prevents reconstruction. The word “minimum” is justified in Q001 by a feasible named optimizer, and Q002 equates its value with the infimum; neither replaces the interval by a finite comparator set. Definitions C2/C3 accept arbitrary real prediction traces, while Q005/Q006 specifically instantiate the actual C1 predictor. As a semantic example of sign, choosing y_0=0,y_1=1 and p_t=y_t for these two times gives learner loss zero and best fixed comparator loss 1/2, hence C3=−1/2; no assumption here makes arbitrary p causal. This illustration distinguishes signed excess from an absolute or automatically nonnegative quantity and is not an extra target or source claim.

Input byte hashes are checked against manifest rows and rechecked after report creation. No theorem proofs or source identity were supplied in these files; no source, proof, compilation or acceptance judgment is made. Reused staged history and unattested runtime settings remain disclosed.

