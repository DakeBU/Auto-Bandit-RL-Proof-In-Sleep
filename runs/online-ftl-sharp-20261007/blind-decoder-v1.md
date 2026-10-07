# Neutral reconstruction of N01-N13

Actor `/root/osd_blind`; requested GPT-6 Astra / medium without escalation. Runtime model and effort are not independently attested. No human or external-review status or external-independence claim is made.

This is a reused decoder. Prior neutral-interface exposure includes the 20261007 current-support, policy, scalar absolute-loss, linearization, scalar step-minimization, unit-scaling, and foundations packets. It is not a fresh history-free actor. For this task ONLY `online-ftl-sharp-20261007/blind-packet-v1.md` was inspected. No source identity, original alias, theorem body, previous verdict, or other historical material was looked up.

## Exact definitions and notation

All sequences y,z:N->R are arbitrary total real sequences unless a hypothesis constrains a stated prefix. The definitions are
\[
a_n(y)=\frac{\sum_{i=0}^{n-1}y_i}{n},\qquad
b_t(y)=\begin{cases}\tfrac12,&t=0,\\a_t(y),&t>0,\end{cases}
\qquad
c_t=\begin{cases}0,&t=0,\\1,&t>0.\end{cases}
\]
Natural indices in real arithmetic are coerced to R. Empty sums are zero, and real division is totalized, so a_0(y)=0/0=0. Crucially b_0(y)=1/2, not a_0(y). For positive t, b_t uses exactly y_0,...,y_{t-1}. The next mean a_{t+1} includes current y_t. The terminal mean a_T is a single fixed argument used for every loss in its comparison sum.

Define the roundwise difference and the finite cumulative difference
\[
\delta_t(y)=(b_t(y)-y_t)^2-(a_{t+1}(y)-y_t)^2,
\]
\[
\Delta_T(y)=\sum_{t=0}^{T-1}(b_t(y)-y_t)^2
            -\sum_{t=0}^{T-1}(a_T(y)-y_t)^2.
\]
These are different expressions: the second sum in delta uses the changing prefix mean, whereas the second sum in Delta uses the terminal mean throughout. Define
\[
H_T=\frac14+\sum_{j=0}^{T-2}\frac4{j+2},
\]
with its precise formal meaning \(H_T=1/4+\sum_{j\in\operatorname{range}(T-1)}4/((j:\mathbb R)+2)\); natural subtraction is truncated and an empty range contributes zero. Let k_r denote the constant sequence k_r(t)=r.

No probability distribution, expectation, filtration, adaptive adversary assumption, stochastic law, or executable feedback model occurs. These are deterministic properties of the displayed total functions. Their strict-prefix dependence is explicit; there is no separate freely chosen initial predictor beyond the fixed 1/2 branch. A closed typed Prop description is not a supplied proof.

The seven slots for each target are objects; quantifiers; assumptions; conclusion; constants/indices; probability/feedback/information; boundary.

## N01

1. **Objects.** Total real sequences y,z and natural time t; prediction function b.
2. **Quantifiers.** Every y,z:N->R and t:N, conditioned on equality for every i<t.
3. **Assumptions.** \(\forall i\in\mathbb N,\ i<t\Rightarrow y_i=z_i\). No outcome-range assumption.
4. **Conclusion.** Strict-prefix agreement makes the current predictions equal:
   \[\forall y,z,t,\quad(\forall i<t,y_i=z_i)\Rightarrow b_t(y)=b_t(z).\]
5. **Constants/indices.** Prefix excludes current t and all future indices; the output time is the same t on both sides.
6. **Probability/feedback/information.** A deterministic prefix-invariance statement: b_t cannot distinguish sequences with the same strict past. No probabilistic adaptation or equality of current targets is asserted.
7. **Boundary.** At t=0 the premise is vacuous and both values are exactly 1/2. Values outside [0,1] are permitted. The conclusion does not say the two sequences themselves agree at t or later.

## N02

1. **Objects.** Any total real sequence y, natural t, and closed interval [0,1].
2. **Quantifiers.** Every y,t with every strict-past y_i in the interval.
3. **Assumptions.** \(\forall i<t,\ 0\le y_i\le1\). Current y_t is not constrained.
4. **Conclusion.** The current prediction is also in the interval:
   \[\forall y,t,\quad(\forall i<t,y_i\in[0,1])\Rightarrow b_t(y)\in[0,1].\]
5. **Constants/indices.** Exact endpoints 0 and 1; for t>0 b_t is the mean of t terms, not t+1.
6. **Probability/feedback/information.** Deterministic interval preservation from the strict prefix. No expectation or sample-independence premise.
7. **Boundary.** At t=0 no past values need bounding; b_0=1/2 is feasible. For t>0 all-zero/all-one prefixes can give endpoints. No current/future target restriction follows.

## N03

1. **Objects.** Arbitrary y:N->R and natural t; prefix means a_t,a_{t+1}.
2. **Quantifiers.** Every sequence and strictly positive t.
3. **Assumptions.** t>0 only, with no bound on sequence values.
4. **Conclusion.** The new mean is the previous mean plus the current deviation divided by the new count:
   \[\forall y,t,\quad t>0\Rightarrow a_{t+1}(y)=a_t(y)+\frac{y_t-a_t(y)}{t+1}.\]
5. **Constants/indices.** Denominator is the real coercion of t+1, not t. The included new target has index t.
6. **Probability/feedback/information.** Exact algebraic update of means after y_t is included; no gradient or stochastic update interpretation is assumed.
7. **Boundary.** The target excludes t=0 even though totalized means can be evaluated there. It is stated in terms of a, not b, so it must not replace a_0 by b_0=1/2. No approximation or bounded-data requirement.

## N04

1. **Objects.** Sequence y, natural t, current prediction b_t, next mean a_{t+1}, and squared real deviations.
2. **Quantifiers.** Every y,t satisfying a bound on EVERY i<=t, including the current outcome.
3. **Assumptions.** \(\forall i\le t,\ y_i\in[0,1]\).
4. **Conclusion.** The current difference between squared losses is bounded above by 4/(t+1):
   \[\forall y,t,\quad(\forall i\le t,y_i\in[0,1])\Rightarrow\delta_t(y)\le\frac4{t+1}.\]
5. **Constants/indices.** Exact numerator 4, denominator t+1, non-strict <=. The second predictor is a_{t+1}, not a_t or a fixed terminal mean.
6. **Probability/feedback/information.** Compares the strict-past prediction with a mean incorporating current y_t. This is a deterministic numerical comparison, not a claim that both are available before observing y_t.
7. **Boundary.** t=0 is included; denominator equals 1 and bound is 4. The definition uses b_0=1/2 and a_1=y_0. The sharper zero-time bound is a different target. Current boundedness cannot be weakened silently to a strict-prefix-only assumption.

## N05

1. **Objects.** Sequence y, positive natural horizon T, sequential predictions b_t and terminal prefix mean a_T.
2. **Quantifiers.** Every y,T with T>0 and all played targets in [0,1].
3. **Assumptions.** \(T>0\) and \(\forall t<T,y_t\in[0,1]\).
4. **Conclusion.** The cumulative excess over the single terminal mean is bounded by a logarithmic scalar expression:
   \[\forall y,T,\quad[T>0\land(\forall t<T,y_t\in[0,1])]\Rightarrow\Delta_T(y)\le4+4\log T.\]
5. **Constants/indices.** Natural logarithm of the real coercion of T; additive 4 and multiplicative 4 exactly. Both sums run t=0,...,T-1; the comparator mean is a_T in every term.
6. **Probability/feedback/information.** Same y feeds both sums. The comparator mean uses the entire played prefix, while b_t uses only its strict past. No independent comparator variable or expectation is present.
7. **Boundary.** T=0 excluded; no inference from totalized log/division there. At T=1 the RHS is 4. This is an upper bound, not equality, a two-sided estimate, or a claim that the factor 4 is attained.

## N06

1. **Objects.** Any sequence y with bounded y_0, current initial prediction b_0=1/2, and a_1=y_0.
2. **Quantifiers.** Every y:N->R with y_0 in [0,1]; later values unrestricted.
3. **Assumptions.** \(0\le y_0\le1\).
4. **Conclusion.** The first-round difference is at most one-quarter:
   \[\forall y,\quad y_0\in[0,1]\Rightarrow\delta_0(y)=(\tfrac12-y_0)^2\le\tfrac14.\]
   The equality displayed here unpacks the definitions; the target's requested claim is the final inequality.
5. **Constants/indices.** Exact 1/4; compares b at 0 and a at 1, both against y_0.
6. **Probability/feedback/information.** The initial b is fixed before any target; a_1 uses the first target. No stochastic initialization.
7. **Boundary.** Endpoints y_0=0 or 1 permitted; interior values need not attain the bound. Only y_0 is bounded. This does not replace the initial b by empty-prefix a_0=0.

## N07

1. **Objects.** Sequence y, positive natural T, cumulative Delta_T and scalar H_T as defined above.
2. **Quantifiers.** Every y,T with a bounded played prefix and positive horizon.
3. **Assumptions.** T>0 and \(\forall t<T,y_t\in[0,1]\).
4. **Conclusion.** The initial one-quarter term plus the remaining reciprocal sum bounds cumulative excess:
   \[\forall y,T,\quad[T>0\land(\forall t<T,y_t\in[0,1])]\Rightarrow
   \Delta_T(y)\le\frac14+\sum_{j\in\operatorname{range}(T-1)}\frac4{(j:\mathbb R)+2}.\]
5. **Constants/indices.** Sum has T-1 terms, with denominators 2,...,T for T>=2. Constant 1/4 is separate; numerator 4 retained for each later term. Natural subtraction T-1 is literal.
6. **Probability/feedback/information.** Compares sequential predictions and the terminal mean on the same sequence. It does not identify Delta_T with a sum of deltas by definition; the displayed inequality is the target claim.
7. **Boundary.** At T=1 the reciprocal sum is empty and H_1=1/4. T=0 excluded even though range(T-1) is syntactically empty under natural subtraction. It is a bound, not universal equality or proof that later constants are sharp.

## N08

1. **Objects.** Two fixed total sequences k_0 and k_1; their first-round differences.
2. **Quantifiers.** Closed conjunction with no free universal variables. The constant functions specify all times, although only the first target is used.
3. **Assumptions.** None beyond the fixed definitions.
4. **Conclusion.** Both endpoint examples attain one-quarter and satisfy the corresponding upper comparisons:
   \[\delta_0(k_0)=\tfrac14\ \land\ \delta_0(k_1)=\tfrac14\ \land\ \delta_0(k_0)\le\tfrac14\ \land\ \delta_0(k_1)\le\tfrac14.\]
   In each case b_0=1/2 and the one-point mean equals the endpoint target.
5. **Constants/indices.** Exact four conjuncts, two equalities and two non-strict inequalities; no horizon beyond time zero/mean index one.
6. **Probability/feedback/information.** Concrete numerical tests of endpoint behavior, not probabilistic outcomes or a newly quantified family.
7. **Boundary.** These witness attainment of the first-round bound at both endpoints; they do not imply every sequence or every cumulative horizon attains it.

## N09

1. **Objects.** Fixed midpoint sequence k_{1/2}; first-round difference.
2. **Quantifiers.** A closed two-conjunct numerical statement.
3. **Assumptions.** None beyond the specified constant sequence.
4. **Conclusion.** The midpoint difference vanishes and is strictly below one-quarter:
   \[\delta_0(k_{1/2})=0\ \land\ \delta_0(k_{1/2})<\tfrac14.\]
5. **Constants/indices.** b_0=a_1=target=1/2; exact zero and strict <.
6. **Probability/feedback/information.** Both squared deviations evaluate to zero; no uncertainty or randomized prediction.
7. **Boundary.** This is a single interior example, not a universal claim about all interior sequences or later rounds. It distinguishes a non-tight instance from the endpoint examples.

## N10

1. **Objects.** Fixed constant sequence k_2; first-round difference outside the interval hypothesis.
2. **Quantifiers.** Closed conjunction, not universal over unbounded outcomes.
3. **Assumptions.** None; the chosen outcome 2 is explicitly outside [0,1].
4. **Conclusion.** Its first-round difference is nine-quarters and exceeds one-quarter:
   \[\delta_0(k_2)=\tfrac94\ \land\ \delta_0(k_2)>\tfrac14.\]
5. **Constants/indices.** b_0=1/2, a_1=2; difference is (1/2-2)^2-0=9/4.
6. **Probability/feedback/information.** Deterministic test showing a violation of the one-quarter inequality when the bounded-first-target premise is absent.
7. **Boundary.** This does not contradict N06 because y_0=2 fails its hypothesis. No claim is made that every out-of-range target violates every bound or that N04/N05 fail universally.

## N11

1. **Objects.** Constant-zero sequence k_0 and horizon T=1; cumulative difference Delta_1 and bound H_1.
2. **Quantifiers.** Closed numerical conjunction.
3. **Assumptions.** None beyond those fixed values.
4. **Conclusion.** The one-round cumulative difference equals one-quarter and meets the empty-remainder bound:
   \[\Delta_1(k_0)=\tfrac14\ \land\ \Delta_1(k_0)\le\tfrac14+\sum_{j\in\operatorname{range}(1-1)}\frac4{(j:\mathbb R)+2}.\]
5. **Constants/indices.** range 1 contains only t=0; terminal mean index 1. Natural 1-1=0, so RHS=1/4.
6. **Probability/feedback/information.** The sequential sum uses b_0=1/2 and the terminal-mean sum uses a_1=0. This is the literal T=1 cumulative example.
7. **Boundary.** The remainder is empty, not a spurious 4/1 or 4/2 term. No assertion about a zero horizon or about equality for other sequences is added.

## N12

1. **Objects.** The fixed total test sequence c with c_0=0 and c_t=1 for all t>0; horizon 2.
2. **Quantifiers.** Closed conjunction of a value equality, bound comparison, and bound-value equality.
3. **Assumptions.** None beyond c and T=2 as given.
4. **Conclusion.** The two-round cumulative difference is three-quarters, is bounded by H_2, and H_2 equals nine-quarters:
   \[\Delta_2(c)=\tfrac34\ \land\ \Delta_2(c)\le H_2\ \land\ H_2=\tfrac94.\]
   Explicitly b_0=1/2,b_1=a_1=0,a_2=1/2. The sequential sum is 1/4+1=5/4 and the fixed-mean sum is 1/4+1/4=1/2, giving 3/4.
5. **Constants/indices.** The bound sum is range(2-1)=range 1: one term 4/(0+2)=2, hence H_2=1/4+2=9/4. No denominator 1 or 3 is inserted.
6. **Probability/feedback/information.** At time 1 the prediction uses only c_0=0, although c_1=1; terminal a_2 uses both targets. The example preserves this information order.
7. **Boundary.** The displayed bound has slack: 3/4<9/4 follows numerically, while the target explicitly requests only <= for that conjunct. It is not a claim that the cumulative upper bound is attained or that its constant is optimal.

## N13

1. **Objects.** Fixed constant-zero sequence k_0 and fixed sequence c; time t=1.
2. **Quantifiers.** Closed conjunction with no free parameters.
3. **Assumptions.** None beyond the definitions.
4. **Conclusion.** Equal predictions can accompany different current targets:
   \[b_1(k_0)=b_1(c)\ \land\ 0\ne c_1.\]
   Both predictions are zero because both strict prefixes contain only target 0; c_1=1 whereas k_0(1)=0.
5. **Constants/indices.** Time exactly 1, strict past index 0; c_1=1 and common prediction 0. Equality of predictions is not equality of sequences.
6. **Probability/feedback/information.** Concrete demonstration of the strict-prefix distinction: current targets can differ without changing the pre-current prediction. It is not a prediction-accuracy or future-observation claim.
7. **Boundary.** Does not assert equality of later predictions: after differing current targets enter the prefix, later means may differ. No probability or universal target-identifiability statement is supplied.

## Evidence boundary

All thirteen closed propositions are interpreted with their literal assumptions and operations. Universal conditional statements N01-N07 are distinguished from the closed numerical examples N08-N13. The empty mean a_0=0 is never conflated with b_0=1/2. The packet's type declarations and this reconstruction are not target proofs, and no source identity, source-fidelity, proof acceptance, review acceptance, chapter completion, or Goal completion is claimed. No semantic ambiguity blocks this decoding; runtime model/effort remain unattested and inherited neutral history is disclosed.