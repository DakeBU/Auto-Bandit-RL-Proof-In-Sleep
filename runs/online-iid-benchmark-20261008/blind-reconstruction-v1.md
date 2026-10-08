# Neutral reconstruction: C0-C3 and Q001-Q008

Actor /root/osd_blind. Requested GPT-6 Astra / medium; no escalation. Runtime model and effort are not independently attested. The actor is distinct in the requested staged workflow but has reused neutral-decoder history covering earlier scalar, policy, finite-history, limit, lower-bound and minimum interfaces. This is not absolute blindness, first exposure, human or external review, or an independence certification.

Only the current neutral-packet-v1.md, its sole neutral-context-v1.lean input row, and neutral-inputs-v1.json were read. No source identity, public name, proof body, prior verdict or other packet was inspected. The packet and context contain four definitions and eight closed Prop descriptions. Requested type-compilation status is not independently tested here and does not supply proofs. No source/proof/acceptance verdict is made.

## Exact shared notation and assumption bundles

Write \(I=[0,1]\), \(\mathbb E_\mu Z=\int Z\,d\mu\), \(m=\mathbb E_\mu Y_0\), and \(\sigma^2=\operatorname{variance}_\mu(Y_0)\). All outcomes/predictions are real-valued functions on the same supplied measurable space \(\Omega\). Natural T,t are coerced to real in real arithmetic. All sums indexed t<T mean Finset.range T, including zero through T−1.

To give complete formulas without hiding repeated assumptions, define the abbreviation \(\mathcal S(\Omega,\mu,Y)\) to mean exactly:

- \(\Omega:\mathrm{Type*}\) has a supplied measurable-space instance, \(\mu\) is a measure, and IsProbabilityMeasure \(\mu\);
- \(Y:\mathbb N\to\Omega\to\mathbb R\), with \(\forall t,\operatorname{Measurable}(Y_t)\);
- \(\forall t,\operatorname{IdentDistrib}(Y_t,Y_0,\mu,\mu)\);
- \(\forall t,\ Y_t(\omega)\in I\) for \(\mu\)-almost every \(\omega\).

The null exceptional set is permitted to depend on t in this literal quantifier order. This is not a pointwise all-\(\omega\) bound. \(\mathcal S\) does NOT include independence of outcomes. Write \(\mathcal I(Y,\mu)\) for the separately supplied iIndepFun Y μ: joint independence of the indexed random-variable family, not merely equal marginal laws or pairwise independence.

For the explicit policy interface,
\[
\pi_t:\bigl(\{i:\mathbb N\mid i<t\}\to\mathbb R\bigr)\to\mathbb R,\qquad
P^\pi_t(\omega)=\pi_t(i\mapsto Y_i(\omega)).
\]
The finite index type is exactly the subtype of Finset.range t. Its input is the complete strictly past real-coordinate tuple, not the current outcome. The conditions \(\mathcal A(\pi)\) mean \(\forall t,\pi_t\) is measurable on that finite product space, and \(\forall t,z,\pi_t(z)\in I\) POINTWISE for every input tuple, including tuples not arising on the actual sample path. This differs from the almost-sure bound on Y. At t=0 the input type is empty, so \(\pi_0\) produces a fixed value independent of \(\omega\); it need not be 1/2. No independent random seed is an explicit policy argument. Exogenous choices may depend on distribution knowledge; the type does not certify an unknown-law learner.

Set
\[
J_T(u)=\mathbb E_\mu\!\left[\sum_{t<T}(u-Y_t)^2\right],\qquad
A_T(P)=\mathbb E_\mu\!\left[\sum_{t<T}(P_t-Y_t)^2\right].
\]
The comparator u in J_T is a SINGLE deterministic scalar held fixed across times and outcomes. Real Bochner integrals and sInf are totalized operations in the bare definitions; notation alone does not assert measurability/integrability or attainment. The propositions add conditions appropriate to their conclusions. There is no minimization INSIDE the expectation in C0.

Each definition and proposition has seven slots: objects; quantifier order; assumptions; defining equation/conclusion; constants/indices; probability/information; boundaries.

## C0

1. **Objects.** Any measurable space Ω, measure μ, real random-variable stream Y, and T:N.
2. **Quantifier order.** Defined for every Ω,μ,Y,T, with no probability instance required in the definition.
3. **Assumptions.** Only the measurable-space type structure; no measurability/boundedness of Y or same-law/independence assumptions.
4. **Defining equation.** The best FIXED comparator expected objective is
\[
C0(\mu,Y,T)=\operatorname{sInf}\{J_T(u):u\in I\}
=\inf_{u\in I}\mathbb E_\mu\sum_{t<T}(u-Y_t)^2.
\]
5. **Constants/indices.** Full cumulative sum, not average; comparator interval endpoints 0,1. Image set contains real objective VALUES.
6. **Probability/information.** Infimum lies OUTSIDE integration. A comparator cannot vary with ω; this is not \(\mathbb E_\mu[\inf_{u\in I}\sum_{t<T}(u-Y_t)^2]\), nor a pathwise empirical-mean benchmark.
7. **Boundaries.** Bare definition neither names a minimizer nor certifies integrability. T=0 gives zero integrands and image {0}, hence C0=0. Real totalization is not an unconditional expected-loss theorem.

## C1

1. **Objects.** Any measurable Ω, measure μ, Y and arbitrary prediction P:N→Ω→R, T:N.
2. **Quantifier order.** Defined for every such input tuple.
3. **Assumptions.** No probability normalization, causality, measurability, square-integrability, feasibility, or independence premise in the definition.
4. **Defining equation.** Signed expected excess above C0 is
\[
C1(\mu,Y,P,T)=A_T(P)-C0(\mu,Y,T).
\]
5. **Constants/indices.** Difference of an integral and an infimum of integrals, not expectation of a pathwise hindsight regret. No absolute value or division by T.
6. **Probability/information.** P is a supplied random-variable stream, not an algorithm constructed by C1. It could encode current/future data unless later assumptions constrain it.
7. **Boundaries.** T=0 gives zero. Nonnegativity is not built into C1; an unconstrained predictor can correlate with current targets. Meaningful expectation interpretation relies on additional hypotheses rather than integral notation alone.

## C2

1. **Objects.** Deterministic real sequence y:N→R and natural T.
2. **Quantifier order.** Defined for all y,T.
3. **Assumptions.** None.
4. **Defining equation.** Prefix empirical mean:
\[
C2(y,T)=\frac{\sum_{t<T}y_t}{T}.
\]
5. **Constants/indices.** Exactly T terms and denominator real-coerced T.
6. **Probability/information.** Finite prefix arithmetic; when used pathwise, it computes an empirical sample mean, distinct from the distribution mean m.
7. **Boundaries.** Empty sum and total real division give C2(y,0)=0. No interval bound without conditions on the sequence.

## C3

1. **Objects.** Deterministic target sequence y and natural prediction time t.
2. **Quantifier order.** Defined for every y,t.
3. **Assumptions.** None.
4. **Defining equation.** The actual midpoint-initialized strict-prefix predictor is
\[
C3(y,t)=\begin{cases}1/2,&t=0,\\ C2(y,t),&t>0.\end{cases}
\]
5. **Constants/indices.** For t>0 uses y_0,...,y_{t-1}, with denominator t. Current y_t excluded.
6. **Probability/information.** Explicit causal input formula, no comparator or law mean queried. Applied to \(y_i=Y_i(\omega)\), it gives an actual random predictor. This does not identify it with any external named algorithm.
7. **Boundaries.** First prediction fixed at 1/2, not empty mean zero or unknown m. Not pointwise bounded on arbitrary real streams; under the stochastic hypotheses appropriate boundedness is almost sure.

## Q001

1. **Objects.** Ω,μ,Y satisfying \(\mathcal S\), natural T and arbitrary real fixed u.
2. **Quantifier order.** Universally Ω/measurable structure, μ/probability instance, Y, measurability, equal-law and almost-sure bounds, then T and u.
3. **Assumptions.** Exactly \(\mathcal S\); NO independence between different Y_t. u is not restricted to I.
4. **Conclusion.** The fixed comparator expected cumulative square loss decomposes into variance plus squared bias:
\[
\forall\Omega,\mu,Y,T,u,\quad
\mathcal S(\Omega,\mu,Y)\Rightarrow J_T(u)=T\sigma^2+T(u-m)^2.
\]
5. **Constants/indices.** Exact factor T for both terms; no 1/2 or averaging. Variance and mean are those of Y_0.
6. **Probability/information.** Same marginal law suffices for the sum of fixed-comparator expectations; it does not assert independent samples. u is deterministic, not a data-dependent comparator.
7. **Boundaries.** T=0 included with 0=0. Exceptional null sets allowed; no pointwise support requirement. No uniqueness/minimization conclusion in this target alone.

## Q002

1. **Objects.** Same Ω,μ,Y and natural T; real image set \(S_T=\{J_T(u):u\in I\}\).
2. **Quantifier order.** Universally all common inputs with \(\mathcal S\), then T.
3. **Assumptions.** \(\mathcal S\), without independence or T>0.
4. **Conclusion.** The mean is feasible AND T times variance is an attained least value:
\[
\mathcal S\Rightarrow
\left[m\in I\ \land\ \operatorname{IsLeast}(S_T,T\sigma^2)\right].
\]
Expanded, IsLeast asserts BOTH \(T\sigma^2\in S_T\) and \(\forall z\in S_T,T\sigma^2\le z\). It is not only a lower bound or infimum equality.
5. **Constants/indices.** Value Tσ²; the image is a set of scalar expectations, not random losses or minimizer points.
6. **Probability/information.** A fixed comparator (the distribution mean, consistent with Q001) realizes the optimum outside the integral. No hindsight selection per ω.
7. **Boundaries.** T=0 allowed: all comparators have value zero, so uniqueness must not be asserted. Even for positive T, uniqueness is not an explicit conjunct here. Bounds on outcomes are almost sure.

## Q003

1. **Objects.** Ω,μ,Y,T and C0.
2. **Quantifier order.** Every common input tuple satisfying \(\mathcal S\), then every T.
3. **Assumptions.** \(\mathcal S\) only; no independent outcomes.
4. **Conclusion.** The infimum benchmark value is exactly
\[
\forall\Omega,\mu,Y,T,\quad\mathcal S\Rightarrow C0(\mu,Y,T)=T\sigma^2.
\]
5. **Constants/indices.** Unnormalized cumulative benchmark; variance of Y_0 and real T.
6. **Probability/information.** An equality for the infimum of expected fixed-comparator losses, not for expected pathwise minimum losses.
7. **Boundaries.** T=0 valid. It does not assume the distribution mean is known to any learner or assert an empirical mean achieves this benchmark as a random comparator.

## Q004

1. **Objects.** Common Ω,μ,Y, supplied real random prediction sequence P, and T.
2. **Quantifier order.** First common hypotheses; then P with its two all-time conditions; then arbitrary natural T.
3. **Assumptions.** \(\mathcal S\), \(\forall t,\operatorname{MemLp}(P_t,2,\mu)\), and \(\forall t,\operatorname{IndepFun}(P_t,Y_t,\mu)\). No iIndepFun Y premise, no interval bound on P, and no actual history-policy definition.
4. **Conclusion.** Expected loss excess above Tσ² is the sum of squared prediction deviations from the mean:
\[
\forall\Omega,\mu,Y,P,T,\quad
[\mathcal S\land(\forall t,P_t\in L^2(\mu))\land(\forall t,P_t\perp_\mu Y_t)]
\Rightarrow A_T(P)-T\sigma^2=\sum_{t<T}\mathbb E_\mu(P_t-m)^2.
\]
MemLp includes the library's appropriate almost-everywhere measurability and finite L² condition; it is not being replaced by an unstated pointwise measurable/interval-bound premise.
5. **Constants/indices.** Each P_t is compared to current Y_t for independence and to the same m inside its squared deviation. No cross-time covariance term appears.
6. **Probability/information.** This is a consumer of SUPPLIED current prediction/target independence. It neither constructs P from the past nor proves arbitrary causal rules are independent under same-law alone.
7. **Boundaries.** T=0 both sides zero. Predictions can lie outside I if square-integrable. Dependence among the targets is allowed so long as the stated P_t/Y_t independence holds. No oracle implementability claim.

## Q005

1. **Objects.** Common Ω,μ,Y, explicit finite-history policy π, actual induced \(P^\pi_t\), T.
2. **Quantifier order.** First \(\mathcal S\), then independent-family condition \(\mathcal I\), then π with measurability and pointwise all-input feasibility, then T.
3. **Assumptions.** \(\mathcal S\land\mathcal I\land\mathcal A(\pi)\). No separate supplied hP/hInd for the predictions appears; the target concerns the explicitly constructed strict-past policy.
4. **Conclusion.** Its excess is exactly a sum of mean-square deviations and is nonnegative:
\[
\forall\Omega,\mu,Y,\pi,T,\quad
[\mathcal S\land\mathcal I\land\mathcal A(\pi)]
\Rightarrow
\left[C1(\mu,Y,P^\pi,T)=\sum_{t<T}\mathbb E_\mu(P^\pi_t-m)^2
\ \land\ 0\le C1(\mu,Y,P^\pi,T)\right].
\]
5. **Constants/indices.** Policy input indexed by subtype range t, hence exactly 0,...,t−1. Two conjuncts, equality then nonnegativity.
6. **Probability/information.** Joint independence of Y is separate from common law. Finite strict-past construction links actual predictions to that independence setting; current Y_t is not in π_t's input. No separate runtime seed input is defined.
7. **Boundaries.** T=0 included; π_0 sees an empty tuple and may be any fixed feasible scalar. Pointwise bound on π for ALL tuples is stronger than almost-sure outcome bounds and must not be silently weakened. This result is not for a policy seeing the current target.

## Q006

1. **Objects.** Ω,μ,Y,T and actual predictor \(P^*_t(\omega)=C3((i\mapsto Y_i(\omega)),t)\).
2. **Quantifier order.** Universally common inputs satisfying \(\mathcal S\), then \(\mathcal I\), then T; no free policy parameter.
3. **Assumptions.** \(\mathcal S\land\mathcal I\). No explicit pointwise all-input bound on C3 is stated; arbitrary real input tuples could yield means outside I, while the actual outcomes are bounded almost surely.
4. **Conclusion.**
\[
\forall\Omega,\mu,Y,T,\quad[\mathcal S\land\mathcal I]\Rightarrow
\left[C1(\mu,Y,P^*,T)=\sum_{t<T}\mathbb E_\mu(P^*_t-m)^2
\ \land\ 0\le C1(\mu,Y,P^*,T)\right].
\]
The midpoint/prefix-mean path is the same one used in both the expected loss and right-hand deviations.
5. **Constants/indices.** P*_0=1/2; for t>0 denominator t with t strictly past samples. m remains the distribution mean, distinct from each sample mean.
6. **Probability/information.** This is an actual specified predictor, not the abstract independence consumer of Q004. It uses no oracle m. The supplied independent-family condition remains essential to the scope of the proposition.
7. **Boundaries.** T=0 equality zero. No explicit logarithmic rate, convergence guarantee, or pointwise support of Y is included. The formula is not asserted to meet Q005's bound for every hypothetical out-of-range input tuple.

## Q007

1. **Objects.** Ω,μ,Y,T and the constant predictor \(P^m_t(\omega)=m\).
2. **Quantifier order.** All common inputs under \(\mathcal S\), then T.
3. **Assumptions.** \(\mathcal S\) only; independence of the outcomes is NOT required.
4. **Conclusion.** The distribution mean is feasible and its constant oracle predictor attains zero expected excess:
\[
\forall\Omega,\mu,Y,T,\quad\mathcal S\Rightarrow
[m\in I\ \land\ C1(\mu,Y,P^m,T)=0].
\]
5. **Constants/indices.** Same m at every time and every ω; exact zero rather than a rate or inequality.
6. **Probability/information.** This is an oracle distribution-mean construction, not a claim that a learner without knowledge of the distribution can compute m from a finite prefix. No empirical-mean substitution is legitimate.
7. **Boundaries.** T=0 valid; no unique optimal policy claim. Equal-law dependent outcomes are within scope. A feasible minimizer of expected fixed loss is different from a pathwise hindsight optimum.

## Q008

1. **Objects.** Ω,μ,Y, finite strict-history π, induced Pπ, POSITIVE T.
2. **Quantifier order.** Common assumptions, independent-family condition, policy with measurable and pointwise bounded outputs, then T and hT:T>0.
3. **Assumptions.** \(\mathcal S\land\mathcal I\land\mathcal A(\pi)\land T>0\), retained even if some are stronger than necessary for an algebraic rearrangement.
4. **Conclusion.** Average expected prediction loss minus variance equals normalized expected excess:
\[
\forall\Omega,\mu,Y,\pi,T,\quad
[\mathcal S\land\mathcal I\land\mathcal A(\pi)\land T>0]
\Rightarrow
\frac{A_T(P^\pi)}{T}-\sigma^2
=\frac{C1(\mu,Y,P^\pi,T)}{T}.
\]
5. **Constants/indices.** Both denominators are the same real T. Variance is subtracted AFTER division on the left; not variance divided by T.
6. **Probability/information.** Relates two normalizations of the same actual expected cumulative loss and fixed-law benchmark. Does not exchange infimum and expectation, and does not supply an asymptotic limit.
7. **Boundaries.** T=0 excluded: totalized zero division would give left side −σ² and right side zero in general. No almost-sure version or stochastic convergence rate is asserted.

## Ambiguities and scope observations

No ambiguity in the actual typed packet prevents reconstruction. The following are substantive limits, not source/proof judgments:

- C0 minimizes a scalar EXPECTED objective outside integration. This is not the expected empirical minimum; Q002's IsLeast includes membership/attainment in the actual image set.
- Common marginal law in \(\mathcal S\) does not include independent samples; iIndepFun is separately present only where stated.
- Outcome support is almost sure for each t, whereas abstract policy boundedness in Q005/Q008 is pointwise for every possible input tuple. C3 has only the path-relevant almost-sure boundedness context, not arbitrary-tuple clipping.
- Q004 assumes square-integrable predictions independent of their current targets; Q005/Q006 concern genuinely specified strict-history inputs. The former alone does not establish causality of arbitrary supplied predictions.
- The oracle mean predictor in Q007 presupposes the mathematical distribution mean; no unknown-distribution learning implementation follows.
- Zero horizons are included through Q007; only Q008 requires T>0 for the displayed normalization. No uniqueness at T=0 is inferred.
- Mere definitions of real Bochner integral and sInf do not certify expectation/minimum interpretations without appropriate hypotheses. The task supplies typed proposition descriptions, not target proofs.

Two fixed input rows and their manifest bindings are checked by raw-byte SHA256 before and after output creation. Runtime settings remain unattested and reused staged history is disclosed. Source, proof and acceptance remain unassessed.

