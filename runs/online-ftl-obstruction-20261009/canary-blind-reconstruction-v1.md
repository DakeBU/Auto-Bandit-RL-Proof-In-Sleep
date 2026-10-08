# Neutral canary reconstruction

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, with no runtime model/effort attestation. This reused automated actor retains prior staged decoder/project history. No absolute blindness, human review or external independence is claimed. Only the two designated neutral inputs and the authorized hash manifest were read; the manifest was used only for input binding. Eleven theorem target types are reconstructed, not proved or compiled. No source, body or chapter acceptance is inferred. The supplied recursion's termination annotation is context, not evidence that the eleven target bodies have been verified.

## Literal context

Let d be the fixed real sequence
\[
d_0=0,\qquad d_{n+1}=1-d_{\lfloor n/2\rfloor}.
\]
The recursive division is natural-number division of the predecessor n, not of n+1. Define
\[
\bar d_T=\frac{\sum_{t<T}d_t}{T},\quad p_0=\tfrac12,\quad p_t=\bar d_t\ (t>0),
\]
\[
R_T(u)=\sum_{t<T}(p_t-d_t)^2-\sum_{t<T}(u-d_t)^2,\qquad
G_T=\sum_{t<T}(p_t-d_t)^2-\inf\{\sum_{t<T}(u-d_t)^2:u\in[0,1]\}.
\]
p is the actual meanPredict rule on this one infinite sequence; at time t it reads only indices i<t. The comparator infimum is real `sInf` over a continuum of fixed constants for the realized prefix. There is no probability, expectation, seed or stochastic law in these targets. Bare infimum notation does not by itself assert attainment or uniqueness.

All sums use the finite range 0,...,T-1. Real denominators are coerced from naturals. Totalized division gives \(\bar d_0=0\), \(R_0(u)=G_0=0\), and normalized zero-horizon regrets zero; the initial prediction remains 1/2. All limits are ordinary real limits along natural indices tending to infinity.

For concise exact expansions set
\[
U\equiv\forall u\in[0,1]\ \forall\varepsilon\in\mathbb R,
\quad\varepsilon>0\Rightarrow\exists N\in\mathbb N\ \forall T\ge N,\ R_T(u)/T\le\varepsilon,
\]
\[
L\equiv\forall u\in[0,1],\quad\exists a\in\mathbb R,\ a\le0\land R_T(u)/T\to a,
\qquad E\equiv\exists m\in[0,1],\ \bar d_T\to m.
\]
These are exactly `NoRegret`, `LimitNoRegret`, and the feasible mean-limit assertion for the given loss and actual p. In U, N can depend on u and ε; the bound is one-sided and is not an absolute-value bound. In L, each comparator has its own potentially negative finite real limit. Nothing requires a single common a or zero for all comparators.

## 1. dyadic_unit_and_prefix

Every observation is feasible, and the first four observations are 0,1,1,0:
\[
(\forall t\in\mathbb N,d_t\in[0,1])\land d_0=0\land d_1=1\land d_2=1\land d_3=0.
\]

1. **Objects:** fixed recursively defined real stream and unit interval.
2. **Quantifiers:** closed conjunction; only the feasibility conjunct quantifies all natural times.
3. **Assumptions:** no external premises beyond the definition of d.
4. **Conclusion:** pointwise support and exact prefix values, not a regret guarantee.
5. **Constants/indices:** endpoints 0,1 and times 0,1,2,3; the recurrence gives two initial ones after zero.
6. **Probability/information:** deterministic every-time condition, not almost-sure support.
7. **Boundaries:** these values are nonconstant and distinguish this stream from simple alternation; no mean convergence is asserted.

## 2. actual_causal_predictions

The actual strict-history predictions at the first four times are
\[
p_0=\tfrac12\land p_1=0\land p_2=\tfrac12\land p_3=\tfrac23.
\]

1. **Objects:** actual meanPredict on d, not a separately supplied prediction trace.
2. **Quantifiers:** closed four-part conjunction.
3. **Assumptions:** fixed definitions only.
4. **Conclusion:** exact outputs of the initialized strict-past rule.
5. **Constants/indices:** p3 averages d0,d1,d2=0,1,1, excluding d3; p0 is 1/2 rather than empty mean zero.
6. **Probability/information:** no current observation is read by p_t; no randomness.
7. **Boundaries:** not predictions equal to current observations or a horizon-dependent oracle. No all-time rate or limit follows from these four values alone.

## 3. actual_signed_regrets

The best-comparator gaps are zero at horizon zero and positive at horizons one through three, while normalized regret against fixed comparator zero is negative at horizon three:
\[
G_0=0\land G_1=\tfrac14\land G_2=\tfrac34\land G_3=\tfrac56
\land R_3(0)/3=-\tfrac16.
\]

1. **Objects:** realized feasible-best regret and fixed-zero comparator regret for the same actual sequence and predictions.
2. **Quantifiers:** closed conjunction of five numerical equalities.
3. **Assumptions:** fixed context only, without a positivity premise.
4. **Conclusion:** four cumulative best-regret values and one normalized signed fixed-comparator value; they are different metrics.
5. **Constants/indices:** horizons 0,1,2,3; only the last expression is divided by 3. The negative sign belongs to -1/6, not to G3=5/6.
6. **Probability/information:** deterministic finite losses; best comparator uses full prefix, whereas predictions use strict history.
7. **Boundaries:** positive best regret does not require every fixed-comparator regret to be positive. This finite negative value does not establish a negative asymptotic limit.

## 4. all_comparator_iff_instantiated

For this specific actual process, ordinary-limit no-regret is equivalent to a feasible empirical-mean limit:
\[
L\Longleftrightarrow E.
\]
Expanded, the left is \(\forall u\in[0,1],\exists a\le0,R_T(u)/T\to a\); the right is \(\exists m\in[0,1],\bar d_T\to m\).

1. **Objects:** actual process, all feasible constant comparators, empirical means and real limits.
2. **Quantifiers:** closed biconditional with the inner quantifiers just expanded; the comparator precedes its own witness a.
3. **Assumptions:** no supplied mean-limit or regret-limit hypothesis.
4. **Conclusion:** equivalence, not assertion that either side holds. It is a concrete instantiation-shaped target, not by itself verification of a general theorem.
5. **Constants/indices:** feasible interval [0,1], nonpositive a, ordinary natural-horizon limits; T0 values are finite and irrelevant to atTop.
6. **Probability/information:** deterministic signed fixed-comparator limits, not expectations or a high-probability statement.
7. **Boundaries:** does not replace ordinary limits by U; both sides may fail consistently with the biconditional.

## 5. no_feasible_mean_limit

The empirical mean has no limit in the feasible interval:
\[
\neg\exists m\in[0,1],\quad\bar d_T\longrightarrow m.
\]

1. **Objects:** real empirical-mean sequence and feasible real candidates.
2. **Quantifiers:** negation of an existential m with both interval membership and ordinary convergence.
3. **Assumptions:** fixed d only; no subsequence premise is supplied in this header.
4. **Conclusion:** nonexistence of a feasible ordinary mean limit.
5. **Constants/indices:** interval [0,1]; T ranges over natural horizons, including a harmless initial empty-prefix value.
6. **Probability/information:** no measure or AE qualification.
7. **Boundaries:** the exact statement explicitly excludes feasible limits; extending it to every real candidate uses further facts, not an enlarged quantifier silently inserted here. It is not a claim that each empirical mean is infeasible.

## 6. two_actual_mean_subsequences

Two exact subsequences of the same empirical-mean sequence have distinct limits:
\[
\bar d_{4^{n+1}-1}\longrightarrow\tfrac23
\quad\land\quad
\bar d_{2\cdot4^n-1}\longrightarrow\tfrac13
\qquad(n\to\infty).
\]

1. **Objects:** actual d, empirical means and two natural horizon maps.
2. **Quantifiers:** closed conjunction of ordinary limits in n; each function uses its own natural n binder.
3. **Assumptions:** no external sequence or convergence premises.
4. **Conclusion:** two actual mean subsequence limits, not direct regret-subsequence values or merely bounds.
5. **Constants/indices:** exactly 4^(n+1)-1 and 2*4^n-1 with natural arithmetic; initial horizons are 3 and 1 and both grow unbounded. Prefix horizon excludes that indexed observation. Neither subsequence uses T0.
6. **Probability/information:** deterministic subsequences of one stream, not separate processes or random stopping times.
7. **Boundaries:** distinct values express nondegenerate oscillation of means; no exact finite-prefix sum formula or convergence rate is included.

## 7. obstruction_instantiated

For the same actual stream, upper no-regret and vanishing normalized best regret coexist with failure of any real fixed-zero regret limit and failure of literal ordinary-limit no-regret:
\[
U\land(G_T/T\to0)\land\neg\exists a\in\mathbb R,(R_T(0)/T\to a)\land\neg L.
\]

1. **Objects:** same p and d, signed fixed comparator and best-regret metrics, upper and ordinary-limit conditions.
2. **Quantifiers:** four-part closed conjunction. U has ∀u∈I,∀ε>0,eventual-T order; the third excludes every real a for one comparator u=0.
3. **Assumptions:** none beyond fixed context; each conjunct is a target conclusion, not a premise.
4. **Conclusion:** exact coexistence of two success conditions and two ordinary-limit failures, without contradiction because the conditions differ.
5. **Constants/indices:** fixed comparator 0 is feasible; best-average target 0; real T denominators. T0 quotients are zero and do not explain the asymptotic failure.
6. **Probability/information:** deterministic actual process, no expectation, current-observation access or horizon-specific replacement.
7. **Boundaries:** no claim that all comparators lack limits or that upper no-regret fails. The no-limit clause rules out every finite real value, not only zero or nonpositive values; extended-real convergence is not addressed.

## 8. upper_noRegret_on_actual_stream

Every feasible constant comparator satisfies the eventual one-sided average-regret upper condition:
\[
\forall u\in[0,1]\ \forall\varepsilon>0,\quad
\exists N\in\mathbb N\ \forall T\ge N,\quad R_T(u)/T\le\varepsilon.
\]

1. **Objects:** all feasible constants and normalized comparator-regret sequences for actual d,p.
2. **Quantifiers:** u, membership, real ε, positivity, then eventual threshold N and all T≥N.
3. **Assumptions:** no additional premise; ε>0 is the local antecedent in the exact predicate.
4. **Conclusion:** the literal NoRegret upper condition U.
5. **Constants/indices:** interval [0,1]; tolerance is any positive real, not ε=0. Empty-horizon value need not be part of the eventual tail.
6. **Probability/information:** deterministic and comparatorwise; no random failure probability.
7. **Boundaries:** not convergence of |R_T|/T or R_T/T to zero, not a uniform threshold for all u, and no eventual exact nonpositivity requirement.

## 9. actual_best_average_zero

The actual process's normalized feasible-best regret converges to zero:
\[
G_T/T\longrightarrow0.
\]

1. **Objects:** realized-prefix feasible comparator infimum, actual prediction loss and natural-horizon ratio.
2. **Quantifiers:** closed ordinary real limit along T→∞.
3. **Assumptions:** no mean-convergence premise is supplied.
4. **Conclusion:** actual two-sided ordinary convergence of this best-regret ratio, not merely an eventual upper bound.
5. **Constants/indices:** target 0, denominator real T, G0/0=0; positive finite values at T1,T2,T3 are compatible.
6. **Probability/information:** no expectation; comparator optimization uses the realized finite prefix.
7. **Boundaries:** does not imply existence of ordinary limits of each signed fixed-comparator ratio. No numerical rate is stated.

## 10. fixed_zero_has_no_ordinary_limit

The normalized regret against the single fixed comparator zero has no finite real limit:
\[
\neg\exists a\in\mathbb R,\quad R_T(0)/T\longrightarrow a.
\]

1. **Objects:** fixed feasible u=0 and one signed normalized comparator-regret sequence.
2. **Quantifiers:** negated existential over every real a, with natural-horizon limit inside.
3. **Assumptions:** fixed context only.
4. **Conclusion:** failure of ordinary real convergence, not just failure of convergence to 0.
5. **Constants/indices:** comparator zero, real T normalization; finite value at T3 is -1/6 from a separate target and does not determine any limit.
6. **Probability/information:** deterministic same run at every horizon.
7. **Boundaries:** does not state positive asymptotic regret, failure of U, lack of boundedness, or nonconvergence for every comparator. No assertion about an extended-real limit is included.

## 11. literal_limit_noRegret_fails

The exact all-feasible-comparator ordinary-limit predicate fails:
\[
\neg\left[\forall u\in[0,1],\quad\exists a\in\mathbb R,
\ a\le0\land R_T(u)/T\to a\right].
\]

1. **Objects:** actual stream/predictor, feasible constants, signed regrets and comparator-dependent limit witnesses.
2. **Quantifiers:** outer negation of ∀u∈I followed by ∃a and its sign/convergence conjunction.
3. **Assumptions:** no new premise.
4. **Conclusion:** failure of literal LimitNoRegret, which needs real convergence for every comparator.
5. **Constants/indices:** feasible interval endpoints 0,1 and sign a≤0; all limits are at natural infinity, independent of the T0 convention.
6. **Probability/information:** deterministic comparatorwise condition; neither a probability statement nor samplewise exception is involved.
7. **Boundaries:** negation alone need not mean every comparator fails. The separate fixed-zero target specifies an actual comparator with no real limit; upper no-regret remains a separately asserted success.

## Coverage and ambiguities

No blocking mathematical ambiguity was found. Exact finite predictions and positive best gaps, a negative normalized fixed gap, two distinct positive-index mean subsequence limits, and the split between U and L express nondegenerate target coverage. Targets 7–11 include a bundled obstruction and its separate components; they are not five independent runtime verifications. None of these supplied headers proves the corresponding general endpoint or supplies body, compilation or source-acceptance evidence.
