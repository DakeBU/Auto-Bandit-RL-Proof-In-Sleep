# Canary statement reconstruction

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, runtime unverified. This reused automated decoder retains previous staged history; no absolute blindness, human review or external independence is claimed. Only the two designated current inputs were read. The twelve targets below are supplied theorem types without proof bodies. Their mathematical content is reconstructed, not certified as proved, compiled, source-faithful or accepted. In particular, canary target types do not verify all five earlier main endpoints.

## Definitions and scope

Fix the deterministic alternating sequence \(y_t=0\) for even t and \(y_t=1\) for odd t, starting 0,1,0,1,... . Define
\[
\bar y_T=\frac{\sum_{t<T}y_t}{T},\quad p_0=\tfrac12,\quad p_t=\bar y_t\ (t>0),
\quad R_T(u)=\sum_{t<T}(p_t-y_t)^2-\sum_{t<T}(u-y_t)^2,
\]
\[
G_T=\sum_{t<T}(p_t-y_t)^2-\inf\{\sum_{t<T}(u-y_t)^2:u\in[0,1]\}.
\]
Natural denominators are coerced to reals; division by zero is totalized. Hence \(\bar y_0=0\), unlike \(p_0=1/2\), and \(R_0(u)=G_0=0\). The infimum is over fixed comparators for a realized finite prefix, not over a finite candidate set. No expectation or probability measure occurs. Prediction at t reads only observations i<t, while \(\bar y_T\) as comparator can use the entire scored prefix.

All limits below are ordinary real limits along natural T to infinity, not just limsup bounds. The literal predicate in target 12 expands to \(\forall u\in[0,1],\exists a\in\mathbb R,a\le0\land R_T(u)/T\to a\); a may depend on u. It does not demand a common limit or a zero limit for all comparators.

## 1. alternating_unit

The sequence is pointwise feasible at every time and has the two specified distinct initial observations:
\[
(\forall t\in\mathbb N,y_t\in[0,1])\land y_0=0\land y_1=1.
\]

1. **Objects:** fixed alternating real sequence and feasible interval.
2. **Quantifiers:** closed conjunction; every natural t is quantified in the first conjunct only.
3. **Assumptions:** no free hypotheses; y is the given parity definition.
4. **Conclusion:** feasibility and two exact initial values.
5. **Constants/indices:** endpoints 0,1 and indices 0,1; no horizon division.
6. **Probability/information:** deterministic pointwise claim, not AE support or an iid model.
7. **Boundaries:** distinct initial values express a nonconstant sequence, not stochastic nondegeneracy; no learning guarantee is asserted.

## 2. alternating_prefix_sum

Every prefix contains exactly the natural-number quotient T/2 ones:
\[
\forall T\in\mathbb N,\quad\sum_{t<T}y_t=\operatorname{real}(\lfloor T/2\rfloor).
\]

1. **Objects:** fixed sequence, finite prefix and real sum.
2. **Quantifiers:** universal natural T.
3. **Assumptions:** none beyond the definition of y.
4. **Conclusion:** exact finite counting identity; a prefix-sum producer target rather than a regret endpoint.
5. **Constants/indices:** sum over 0,...,T-1; division on the right is first natural division by 2, then coercion to ℝ. T0 sum is zero; odd T is not real T/2.
6. **Probability/information:** finite deterministic observations, no expectation.
7. **Boundaries:** does not itself state mean convergence or predictions; parity rounding is essential.

## 3. alternating_mean_tendsto

The actual empirical-mean sequence converges to one half:
\[
\lim_{T\to\infty}\bar y_T=\tfrac12.
\]

1. **Objects:** empirical means of the fixed alternating sequence.
2. **Quantifiers:** closed limit assertion; T varies over naturals inside the function.
3. **Assumptions:** no supplied convergence hypothesis; convergence is the target conclusion.
4. **Conclusion:** ordinary real convergence, supplying the mean-convergence property for this concrete example if proved.
5. **Constants/indices:** limit 1/2; \(\bar y_0=0\) does not affect atTop convergence.
6. **Probability/information:** deterministic prefix average, not expectation or almost-sure convergence.
7. **Boundaries:** a conclusion-producing target, not merely an implication assuming its own result; no rate or regret statement here.

## 4. alternating_initial_predictions

The first four actual predictions are
\[
p_0=\tfrac12\land p_1=0\land p_2=\tfrac12\land p_3=\tfrac13.
\]

1. **Objects:** explicit strict-history mean prediction sequence.
2. **Quantifiers:** closed four-part conjunction.
3. **Assumptions:** only the given definitions.
4. **Conclusion:** exact output values, distinguishing initialization from nonempty prefix averaging.
5. **Constants/indices:** times 0,1,2,3 and real denominators 2,3. p3 averages observations 0,1,0, not the current y3=1.
6. **Probability/information:** actual causal outputs; no supplied surrogate prediction trace.
7. **Boundaries:** no claim that predictions equal current observations or remain constant; p0 differs from empty empirical mean.

## 5. alternating_best_regret_zero_one_two

The feasible-best regret at horizons zero, one and two is exactly
\[
G_0=0\land G_1=\tfrac14\land G_2=\tfrac34.
\]

1. **Objects:** actual p and realized-prefix infimum over constant feasible comparators.
2. **Quantifiers:** closed three-part numerical conjunction.
3. **Assumptions:** fixed y and p only.
4. **Conclusion:** exact best-regret values; the two positive-horizon values are nonzero.
5. **Constants/indices:** T0 empty sum, T1 scores t0, T2 scores t0 and t1. Values are cumulative, not divided by T.
6. **Probability/information:** deterministic losses against the prefix's best constant, with no expectation.
7. **Boundaries:** positive finite values do not contradict normalized convergence to zero; these are not fixed-u regret values for one comparator used at every horizon.

## 6. alternating_actual_gap_nonneg

At every horizon, actual prediction loss is no smaller than the loss of its horizon empirical-mean comparator:
\[
\forall T\in\mathbb N,\quad 0\le R_T(\bar y_T).
\]

1. **Objects:** actual mean predictor, horizon empirical mean and squared comparator regret.
2. **Quantifiers:** arbitrary T; comparator is determined after T as \(\bar y_T\).
3. **Assumptions:** no new premise; fixed alternating sequence.
4. **Conclusion:** nonnegative signed gap against this specified comparator; a concrete instantiation-shaped target for the actual rule.
5. **Constants/indices:** all t<T; T0 yields 0≤0, mean comparator zero.
6. **Probability/information:** p uses strict past, comparison mean uses whole scored prefix; deterministic.
7. **Boundaries:** not nonnegativity against every fixed u and not an upper bound. No proof of a general endpoint is provided by the target type.

## 7. alternating_fixed_decomposition

For any real comparator and horizon, fixed-comparator regret decomposes with a negative squared-distance correction:
\[
\forall u\in\mathbb R\ \forall T\in\mathbb N,\quad
R_T(u)=R_T(\bar y_T)-T(u-\bar y_T)^2.
\]

1. **Objects:** arbitrary fixed real u, natural T, same actual p and horizon mean.
2. **Quantifiers:** u then T; no feasible-domain restriction on u.
3. **Assumptions:** no additional hypotheses.
4. **Conclusion:** exact equality with subtraction, not addition, of the nonnegative correction.
5. **Constants/indices:** real factor T and exponent 2; at T0 all terms vanish even for arbitrary u.
6. **Probability/information:** deterministic fixed-comparator comparison; horizon mean is a comparison device, not an oracle input to prediction.
7. **Boundaries:** permits negative fixed-comparator regret; no independent limit claim or common-comparator optimum assertion.

## 8. alternating_best_average_zero

The normalized feasible-best regret for this actual nonconstant example tends to zero:
\[
\lim_{T\to\infty}G_T/T=0.
\]

1. **Objects:** realized best-regret sequence of fixed alternating y and actual p.
2. **Quantifiers:** closed ordinary-limit assertion over natural T.
3. **Assumptions:** no explicit bound or convergence hypothesis is consumed in this target; the sequence is fixed.
4. **Conclusion:** actual convergence to zero, rather than an equivalence or one-sided limsup condition.
5. **Constants/indices:** real T denominator; G0/0=0 under total division; nonzero finite values at T1,T2 can coexist with this limit.
6. **Probability/information:** no randomness or expected-loss benchmark; comparator infimum is over the realized prefix.
7. **Boundaries:** no finite rate, exact G_T formula or zero normalized fixed-u limit for every u is asserted.

## 9. alternating_fixed_limit_criterion

For any real comparator u and candidate limit a, normalized fixed regret tends to a exactly when squared distance from the empirical mean tends to -a:
\[
\forall u,a\in\mathbb R,\quad
[R_T(u)/T\to a]\ \Longleftrightarrow\ [(u-\bar y_T)^2\to-a].
\]

1. **Objects:** arbitrary real u,a and the two deterministic real sequences.
2. **Quantifiers:** u then a, then a biconditional of ordinary limits along natural horizons.
3. **Assumptions:** no a≤0 or u∈[0,1] premise.
4. **Conclusion:** equivalence, not by itself either limit's existence. The minus sign on a is essential.
5. **Constants/indices:** squared distance, denominator T; at T0 the quotient is zero while squared distance is u², so no pointwise equality is claimed.
6. **Probability/information:** same fixed sequence/comparator on both sides; no expectation.
7. **Boundaries:** any attained a must respect the squared-distance sign, but this is not an extra premise. This target does not establish the universal original endpoint merely by repeating its shape for one sequence.

## 10. alternating_fixed_zero_negative_limit

Against the fixed comparator zero, average signed regret converges to minus one quarter:
\[
\lim_{T\to\infty}R_T(0)/T=-\tfrac14.
\]

1. **Objects:** actual p, fixed feasible comparator u=0, normalized squared regret.
2. **Quantifiers:** closed convergence assertion with T varying naturally.
3. **Assumptions:** no supplied candidate-limit or convergence premise.
4. **Conclusion:** an actual strictly negative ordinary limit, displaying that fixed-comparator regret need not tend to zero.
5. **Constants/indices:** comparator 0, limit -1/4, normalization by real T; T0 quotient is zero and need not match its limit.
6. **Probability/information:** deterministic comparison with a single constant at all times.
7. **Boundaries:** this is not negative best-regret or a claim of negative regret on every finite prefix; it distinguishes signed fixed regret from nonnegative best-comparator gaps.

## 11. alternating_fixed_half_zero_limit

Against the fixed comparator one half, average regret tends to zero:
\[
\lim_{T\to\infty}R_T(1/2)/T=0.
\]

1. **Objects:** same actual process and fixed feasible midpoint comparator.
2. **Quantifiers:** closed ordinary-limit target over natural T.
3. **Assumptions:** no external mean-limit assumption is supplied to this header.
4. **Conclusion:** exact zero limit for this particular fixed comparator.
5. **Constants/indices:** comparator 1/2, limit 0, real T denominator and totalized T0 value zero.
6. **Probability/information:** deterministic sequence; comparator equals the limiting empirical mean but does not replace the strict-history prediction rule.
7. **Boundaries:** does not claim all fixed-comparator limits equal zero. Together with target 10 it tests comparator-dependent limits.

## 12. alternating_literal_limit_noRegret

The literal ordinary-limit no-regret predicate holds on the feasible interval for the actual alternating example:
\[
\forall u\in[0,1],\quad\exists a\in\mathbb R,\quad a\le0\ \land\ R_T(u)/T\to a.
\]

1. **Objects:** feasible set [0,1], losses \((x-y_t)^2\), actual p, fixed comparators and their limit values.
2. **Quantifiers:** each real u and membership u∈I precede an existential real a; the natural-horizon limit is inside that conjunction.
3. **Assumptions:** fixed example only; there is no hidden requirement of a common a across u.
4. **Conclusion:** existence of an ordinary nonpositive real limit for every feasible comparator. This is stronger in form than merely an eventual upper/limsup condition.
5. **Constants/indices:** interval endpoints 0,1; totalized quotient at T0 is zero. Both strictly negative and zero limiting values are allowed.
6. **Probability/information:** deterministic, no expectation or almost-sure quantifier. The predicate applies to the specified actual rule, not all feasible prediction traces.
7. **Boundaries:** the displayed target does not provide an explicit a formula or a convergence rate. Targets 10 and 11 give concrete distinct cases, without proving this all-u target or the earlier universal main theorem.

## Nondegenerate coverage and ambiguity record

The packet expresses twelve distinct canary targets: pointwise binary feasibility and different initial observations; a finite prefix-count identity; a genuine mean-convergence producer; explicit strict-history predictions; positive one/two-horizon best gaps; and concrete instantiation-shaped regret, decomposition and limit goals. In particular, -1/4 against zero versus 0 against one half prevents conflating nonpositive ordinary fixed-comparator limits with zero best-regret average. T0 and odd-prefix rounding are separately represented. These are meaningful specified checks, but no bodies or execution evidence were supplied, so none is described as verified and the five main endpoints are not declared accepted. No blocking mathematical ambiguity was found.
