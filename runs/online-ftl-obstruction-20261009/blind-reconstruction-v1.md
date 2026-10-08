# Neutral statement reconstruction

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, runtime model and effort unverified. This reused automated actor has earlier staged decoder/project history; no absolute blindness, human review or external independence is claimed. Only the designated packet and neutral statement file were read. Four proposition types are reconstructed below without proof, compilation or source-equivalence assessment. The recursion includes a termination annotation/tactic in the supplied context; this is distinct from proof evidence for the four theorem targets.

## Exact definitions

For a real sequence y, write
\[
\bar y_T=\frac{\sum_{t<T}y_t}{T},\qquad
p_t(y)=\begin{cases}1/2,&t=0,\\\bar y_t,&t>0.\end{cases}
\]
All finite sums use indices 0,...,T-1. Natural denominators are coerced to reals and division is totalized: \(\bar y_0=0\), whereas \(p_0=1/2\). At positive time t the prediction is the mean of observations strictly before t; it excludes current y_t and future observations. No random seed, probability measure or stochastic independence appears in this packet.

For squared loss and this actual predictor, define
\[
R_T^y(u)=\sum_{t<T}(p_t(y)-y_t)^2-\sum_{t<T}(u-y_t)^2,
\]
\[
G_T^y=\sum_{t<T}(p_t(y)-y_t)^2-
\inf\left\{\sum_{t<T}(u-y_t)^2:u\in[0,1]\right\}.
\]
The first is signed comparator regret at a specified real constant u. The second uses real `sInf` over the feasible continuum of constants for the realized prefix; it is not an expectation or a minimization over time-varying comparators. The definition alone asserts no attainment or uniqueness. Both vanish at T0 and their normalized zero-horizon values are zero by total division.

The exact two no-regret predicates differ:
\[
\operatorname{Upper}(y)\equiv
\forall u\in[0,1]\ \forall\varepsilon\in\mathbb R,
\quad \varepsilon>0\Rightarrow\exists N\in\mathbb N\ \forall T\ge N,
\quad R_T^y(u)/T\le\varepsilon;
\]
\[
\operatorname{Limit}(y)\equiv
\forall u\in[0,1],\quad\exists a\in\mathbb R,
\quad a\le0\ \land\ R_T^y(u)/T\longrightarrow a.
\]
These expand the displayed `NoRegret` and `LimitNoRegret` for this feasible set/loss/predictor. The threshold N in Upper can depend on both u and ε; there is no uniform-in-u threshold. Upper is a one-sided eventual condition, not convergence of absolute regret or ordinary convergence to zero. In Limit, each comparator can have its own finite nonpositive limit. Every limit below is `atTop` on natural indices to an ordinary real neighborhood filter, not an extended-real limit or only a limsup.

The explicit recursive sequence d is
\[
d_0=0,\qquad d_{n+1}=1-d_{\lfloor n/2\rfloor}\quad(n\in\mathbb N).
\]
The division in the recursive index is natural-number division. Equivalently \(d_j=1-d_{\lfloor(j-1)/2\rfloor}\) for j>0. It is not the recursion using \(\lfloor j/2\rfloor\). Initial values are 0,1,1,0,0,0,0,1,..., illustrating the dependence on the halved predecessor. The formula supplies one fixed infinite deterministic sequence, not separately chosen sequences for different horizons. It alternates values across the binary-tree depth blocks; the unit-interval property below is a separate target, not a premise built into its real-valued type.

## 1. meanPredict_limitNoRegret_iff_mean_converges

For every pointwise feasible real sequence, ordinary-limit no-regret of the actual mean predictor is equivalent to existence of a feasible limit of its empirical means:
\[
\forall y:\mathbb N\to\mathbb R,\quad
[\forall t\in\mathbb N,y_t\in[0,1]]\Longrightarrow
\left(\operatorname{Limit}(y)\Longleftrightarrow
\exists m\in\mathbb R,\ m\in[0,1]\land\bar y_T\longrightarrow m\right).
\]

1. **Objects/spaces:** arbitrary deterministic real sequence, squared loss, actual strict-past mean prediction rule, feasible constants, empirical-mean sequence.
2. **Quantifiers/order:** y, its every-time support proof, then a biconditional. On the left each feasible u precedes its existential nonpositive a. On the right one existential m belongs to [0,1] and is a mean limit.
3. **Assumptions:** only pointwise y_t∈[0,1] for every natural t. Neither side of the equivalence is assumed independently, and no stochastic condition is present.
4. **Conclusion/metric:** equivalence of the exact ordinary-limit no-regret predicate and empirical-mean convergence. This is stronger than merely sufficient mean convergence and does not replace Limit by Upper.
5. **Constants/indices/T0:** interval [0,1], initial prediction 1/2, ordinary limits as T→∞. Empirical mean at zero is 0, regret quotient at zero is 0; both are irrelevant finite initial values.
6. **Probability/information:** deterministic sequence; m describes a limit and is not an input to the predictor. Fixed-comparator limits are signed and may be negative.
7. **Boundaries:** not a claim that every bounded sequence has convergent means, nor that all comparator limits are zero/common. No equivalence with merely vanishing feasible-best regret is stated.

## 2. dyadicObservation_unit

Every entry of the explicit recursive sequence lies in the feasible interval:
\[
\forall t\in\mathbb N,\quad d_t\in[0,1].
\]

1. **Objects/spaces:** the fixed real sequence d defined by the halved-predecessor recursion.
2. **Quantifiers/order:** universal natural time only; no sequence parameter.
3. **Assumptions:** none beyond the supplied recursive definition.
4. **Conclusion/metric:** pointwise feasibility at all times, not a loss or convergence statement.
5. **Constants/indices/T0:** endpoints 0 and 1, d0=0; positive indices follow n+1↦floor(n/2). Binary values are consistent with the explicit recursion, while the exact target only states interval membership.
6. **Probability/information:** no AE qualification; there is no probability measure. This is a deterministic producer target for the premise needed by other interfaces.
7. **Boundaries:** the statement alone does not assert any prefix-average convergence or randomness. The sequence is nonconstant, as its given recursion yields d1=1.

## 3. dyadic_empiricalMean_subsequences

The empirical mean has two specifically indexed subsequences with different ordinary limits:
\[
\lim_{n\to\infty}\bar d_{\,4^{n+1}-1}=\frac23
\quad\land\quad
\lim_{n\to\infty}\bar d_{\,2\cdot4^n-1}=\frac13.
\]

1. **Objects/spaces:** the same fixed recursive sequence, its real empirical means, two natural-index horizon maps and two real limiting values.
2. **Quantifiers/order:** closed conjunction of two `Tendsto` statements. In each, n independently ranges over naturals tending to infinity; neither limit is a hypothesis.
3. **Assumptions:** none beyond context; no supplied convergence premise or separate chosen sequence for either subsequence.
4. **Conclusion/metric:** actual convergence targets for the empirical means along the two maps, with distinct limits 2/3 and 1/3, rather than a direct statement about regret subsequences.
5. **Constants/indices/T0:** horizons are exactly 4^(n+1)-1 and 2*4^n-1 with natural arithmetic/subtraction, not powers of (n-1) or unshifted 4^n. At n0 the horizons are 3 and 1, respectively, so both are positive and grow without bound. A prefix at horizon T excludes observation index T. This target does not use the empty horizon.
6. **Probability/information:** deterministic prefix means of the one full sequence, not expectations or selected random stopping times.
7. **Boundaries:** the unequal limiting values express a genuine ordinary-mean convergence obstruction. This clause does not itself state an exact finite-prefix formula, explicit regret subsequence limits or a rate; those must not be substituted for its two precise assertions.

## 4. dyadic_meanPredict_obstruction

For the actual mean predictor on d, the eventual upper no-regret condition holds and average feasible-best regret tends to zero, yet normalized regret against the feasible comparator zero has no finite real limit; consequently the literal ordinary-limit no-regret property fails:
\[
\operatorname{Upper}(d)
\ \land\ \left[G_T^d/T\longrightarrow0\right]
\ \land\ \left[\neg\exists a\in\mathbb R,\ R_T^d(0)/T\longrightarrow a\right]
\ \land\ \neg\operatorname{Limit}(d).
\]

1. **Objects/spaces:** the single explicit recursive observation sequence, actual initial-half strict-past mean predictor, squared comparator regret, feasible-best regret and both literal no-regret predicates.
2. **Quantifiers/order:** a closed four-part conjunction. The first expands to ∀u∈[0,1],∀ε>0,eventually T. The third negates existence of any real limit a for the one fixed comparator 0, without restricting a's sign. The final conjunct negates the all-feasible-comparator nonpositive-limit property.
3. **Assumptions:** no external hypotheses; all objects are the concrete definitions. No mean-convergence premise is added, and neither upper no-regret nor best-average convergence is a premise in this target: both are asserted conclusions.
4. **Conclusion/metric:** simultaneous one-sided upper control, zero ordinary limit of normalized best regret, failure of any ordinary real limit of normalized zero-comparator regret, and failure of LimitNoRegret. The latter two failures are not claims that the sequence has a positive limit or positive limiting upper bound.
5. **Constants/indices/T0:** feasible comparator 0, limit target zero for G/T, finite sums t<T, real horizon denominator. At T0 both regret quotients are 0; failure to converge is an asymptotic phenomenon and not a division-by-zero issue. The strict-past rule is not altered on subsequences.
6. **Probability/information:** no probabilistic mode; all claims concern the same actual deterministic run. The best comparator is selected from fixed constants using the realized prefix, while the obstruction uses the same comparator u=0 at every horizon.
7. **Boundaries:** upper no-regret and vanishing normalized best regret do not imply existence of ordinary fixed-comparator limits. The no-limit target concerns every finite real a, not merely no nonpositive a; it says nothing here about convergence in an extended-real space. It does not exhibit a violation of the eventual upper condition, nor a failure for every comparator individually.

## Nondegeneracy and ambiguity record

No blocking ambiguity was found. The halved-predecessor recursion is explicit and produces a nonconstant sequence; the two positive, unbounded horizon maps have different mean limits. The final conjunction distinguishes signed fixed-comparator behavior from feasible-best regret and ordinary convergence from an eventual one-sided bound. These are target contents rather than verified results; no proofs, compilation, source comparison or acceptance checks were performed.
