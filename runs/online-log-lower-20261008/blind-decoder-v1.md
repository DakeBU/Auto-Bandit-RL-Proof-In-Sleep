# Neutral reconstruction: r, m, P, law, f1-f8 and N01-N16

Actor `/root/osd_blind`; requested GPT-6 Astra / medium. Runtime model and reasoning effort are not independently attested. This reused actor has staged history from earlier neutral current-support, policy, absolute-loss, linearization, optimal-step, unit-scaling, foundations, sharp-prefix, state, and regret-domain packets. This is not first exposure, human review, external review, or an independence attestation. For this task only `neutral-packet-v1.lean` and `neutral-input-v1.json` in the current run were read. No source identity, map, target proof body, contract, source card, or prior verdict was inspected.

The manifest declares sixteen targets, context-only definitions, and absent proofs. The Lean text indeed defines parameterized values of type Prop, not proofs of those propositions. Their parameter binders determine the universally quantified statements reconstructed below; a proof parameter such as hT is a condition on that instantiation, not a supplied proof of the target. No compilation was run or verified here.

## Exact context and ordering

For arbitrary type X, real losses ell:N->X->R, prediction sequence p:N->X, comparator u:X, and T:N,
\[
r(\ell,p,u,T)=\sum_{t=0}^{T-1}\ell_t(p_t)-\sum_{t=0}^{T-1}\ell_t(u).
\]
It is a signed comparison with a fixed u, not an absolute value or an infimum. For real y:N->R,
\[
m(y,n)=\frac{\sum_{t=0}^{n-1}y_t}{n}.
\]
The count is coerced to real. Empty sum and total real division make m(y,0)=0.

For a finite set arms in X and real weights p:X->R, P(arms,p) is the conjunction of nonnegativity at every member and sum exactly one. It places no condition on p outside arms. Given a measurable space on X,
\[
\operatorname{law}(arms,p)=\sum_{x\in arms}\operatorname{ofReal}(p(x))\,\delta_x.
\]
This measure is defined without P; negative weights are truncated by ENNReal.ofReal, so calling it a normalized probability law requires additional facts. No normalization is implicit in its name.

Write n(h)=length(h) and k(h)=count_true(h). Let q(h)=f1(h) and w(h)=f2(h). Then
\[
q(h)=\frac{k(h)+1}{n(h)+2},\qquad w([])=1,
\]
\[
w(b::h)=w(h)\begin{cases}q(h),&b=\mathrm{true},\\1-q(h),&b=\mathrm{false}.\end{cases}
\]
The recursive list is NEWEST FIRST: the head b is the next/latest target appended to an older history h. The count in q ignores order, but w's recursion and the decoder must retain the declared order.

f3(h,t) is the t-th optional entry of reverse(h), with false as its out-of-range default. Thus f3 presents the stored newest-first list as a chronological stream, oldest first. f4(h,t) is its real indicator, 1 for true and 0 for false. For t>=n(h) these are false and 0 respectively. Finite comparisons below use only t<n(h).

For any deterministic map A:List Bool->R,
\[
f5(A,y,t)=A([y_{t-1},\ldots,y_0]),
\]
where at t=0 the argument is []. The argument is reverse(List.ofFn of the strict prefix). No current y_t or future y is explicitly passed. A is an arbitrary total map; no computability or query model is supplied.

For h of length T, put y_t=f4(h,t), x_t=f5(A,f3(h),t), and \(\bar y=m(f4(h),T)\). The definition f6 is exactly
\[
f6(A,h)=\sum_{t=0}^{T-1}(x_t-y_t)^2-\sum_{t=0}^{T-1}(\bar y-y_t)^2.
\]
The predictions are the SAME actual f5 path associated with A and the chronologically decoded h. The second sum uses one hindsight comparator, the empirical mean of that same full sequence. It is not a fresh path, mean prediction at each t, or comparison with q(h). A has no comparator argument.

The finite weighted functional f7 is
\[
f7(T,F)=\sum_{v:\operatorname{Vector}(\mathrm{Bool},T)}w(v.\mathrm{toList})F(v.\mathrm{toList}).
\]
It is a finite real sum defined for every F, with no measurable-space input and no normalization assumption in its definition. The targets N03-N05 separately assert the nonnegative normalized weights. f8(T), on a supplied measurable space of length-T Boolean vectors, is law(univ,v->w(v.toList)). N06 and N07 additionally require measurable singletons, making the finite atomic probability/integral interpretation explicit. There is no imported continuous latent distribution in these definitions.

H_n below denotes the real coercion of harmonic(n), i.e. \(\sum_{j=1}^{n}1/j\), with H_0=0. All Finset.range indices are zero-based. Seven slots follow for each target: objects; quantifier order; assumptions; conclusion; constants/indices; probability/feedback; exclusions/boundaries.

## N01

1. **Objects:** Any finite Boolean list h, q(h)=f1(h).
2. **Quantifier order:** For every h:List Bool.
3. **Assumptions:** None.
4. **Conclusion:** The smoothed count ratio lies strictly between zero and one:
   \[\forall h,\quad0<q(h)=\frac{k(h)+1}{n(h)+2}<1.\]
5. **Constants/indices:** Numerator pseudocount 1, denominator offset 2; open interval, not closed.
6. **Probability/feedback:** q is computed solely from the supplied finite past list; this target alone does not assert a normalized law over sequences.
7. **Exclusions/boundaries:** Empty h gives 1/2. All-false/all-true lists still give strict interior values. No real-valued non-Boolean history is covered.

## N02

1. **Objects:** Any Boolean h and its two newest-bit extensions.
2. **Quantifier order:** Every h.
3. **Assumptions:** None.
4. **Conclusion:** The two extension weights sum to the parent weight:
   \[\forall h,\quad w(\mathrm{false}::h)+w(\mathrm{true}::h)=w(h).\]
5. **Constants/indices:** Child length n(h)+1; no factor 2 or division by 2.
6. **Probability/feedback:** Splits using q(h) and 1-q(h) for the new head, after the past h; does not reverse this chronological meaning.
7. **Exclusions/boundaries:** h=[] allowed. This identity alone is not the whole nonnegative normalization predicate P.

## N03

1. **Objects:** Arbitrary Boolean list h and real weight w(h).
2. **Quantifier order:** Every h.
3. **Assumptions:** None.
4. **Conclusion:** \(\forall h,\ 0\le w(h)\). Every list weight is nonnegative.
5. **Constants/indices:** Non-strict lower bound zero; no asserted lower numerical constant.
6. **Probability/feedback:** A sign condition on the finite weights, independently of their sum.
7. **Exclusions/boundaries:** Empty list has weight 1. The target does not explicitly assert strict positivity, even if more might follow from definitions.

## N04

1. **Objects:** Natural T and all Boolean vectors of exactly length T.
2. **Quantifier order:** Every T:N, no positive-horizon restriction.
3. **Assumptions:** None.
4. **Conclusion:** Total real weight at fixed length is one:
   \[\forall T,\quad\sum_{v:\operatorname{Vector}(\mathrm{Bool},T)}w(v.\mathrm{toList})=1.\]
5. **Constants/indices:** Exact total 1, not an unweighted sum or sum over all list lengths.
6. **Probability/feedback:** Finite normalization statement; no measurable space needed.
7. **Exclusions/boundaries:** T=0 included: the sole empty vector carries weight 1. Normalization is not itself the separate nonnegativity assertion.

## N05

1. **Objects:** Natural T, univ finite set of Boolean vectors of length T, weight map w.
2. **Quantifier order:** Every T.
3. **Assumptions:** None.
4. **Conclusion:** The explicit normalized-weight predicate holds:
   \[\forall T,\quad P(\mathrm{univ},v\mapsto w(v.\mathrm{toList})),\]
   meaning all these weights are nonnegative and their sum is 1.
5. **Constants/indices:** Fixed length T only; exact unit total.
6. **Probability/feedback:** Certifies the two properties of a discrete weight family, not a sampled trajectory or seed law.
7. **Exclusions/boundaries:** T=0 valid. No topology, measurability, or integrability assumption appears here.

## N06

1. **Objects:** T:N and a measurable space on Boolean vectors of length T with measurable singletons; measure f8(T).
2. **Quantifier order:** Every T and each supplied pair of measurable-space/singleton instances.
3. **Assumptions:** MeasurableSpace and MeasurableSingletonClass on that vector type.
4. **Conclusion:** \(\forall T,\ \operatorname{IsProbabilityMeasure}(f8(T))\) under those instances; f8 has total mass 1.
5. **Constants/indices:** Finite measure constructed with ofReal weights and Dirac masses; no extra renormalization factor.
6. **Probability/feedback:** Converts the specific discrete construction into a probability measure assertion. This is distinct from P's real finite-sum predicate.
7. **Exclusions/boundaries:** Includes T=0. It does not state law(arms,p) is a probability measure for arbitrary weights without conditions.

## N07

1. **Objects:** T:N, the same measurable-space and measurable-singleton structures, arbitrary F:List Bool->R.
2. **Quantifier order:** Every T, every such structure, and every F.
3. **Assumptions:** The two measure-related instances only; no separate measurability or boundedness premise on F in the target.
4. **Conclusion:** The real integral equals the finite weighted sum:
   \[\forall T,F,\quad\int v\ F(v.\mathrm{toList})\,d f8(T)=f7(T,F).\]
5. **Constants/indices:** Only length-T vectors are integrated/summed, with exact weights w.
6. **Probability/feedback:** Identifies the finite functional with a measure expectation under this finite atomic law. Values of F on other lengths do not contribute.
7. **Exclusions/boundaries:** T=0 gives F([]). The missing explicit integrability hypothesis must not be invented: finite measurable-singleton domain provides the setting for the stated identity, not an assertion about arbitrary infinite-domain functions.

## N08

1. **Objects:** Every natural T and the true-count function k on lists.
2. **Quantifier order:** Universal T.
3. **Assumptions:** None.
4. **Conclusion:** Weighted mean true-count is half the length:
   \[\forall T,\quad f7(T,k)=\frac{T}{2}.\]
5. **Constants/indices:** T is coerced to real; exact factor 1/2.
6. **Probability/feedback:** A finite weighted moment under w. No claim that bits are independent fair coins is supplied by this first moment.
7. **Exclusions/boundaries:** T=0 gives zero. Count is number of true entries, unaffected by chronological reversal.

## N09

1. **Objects:** Natural T and squared true-count k(h)^2.
2. **Quantifier order:** Every T.
3. **Assumptions:** None.
4. **Conclusion:** The second raw moment is
   \[\forall T,\quad f7(T,h\mapsto k(h)^2)=\frac{T(2T+1)}6.\]
5. **Constants/indices:** Exact denominator 6 and factor 2T+1; square INSIDE the weighted sum, not square of its mean.
6. **Probability/feedback:** Raw moment of the defined correlated-history weight construction; not a variance formula or independence premise.
7. **Exclusions/boundaries:** T=0 gives zero, T=1 gives 1/2. No replacement by the binomial second moment is justified.

## N10

1. **Objects:** Natural T, ratio q(h) and product q(h)(1-q(h)).
2. **Quantifier order:** Every T.
3. **Assumptions:** None.
4. **Conclusion:** Its finite weighted average is exactly
   \[\forall T,\quad f7(T,h\mapsto q(h)(1-q(h)))=\frac{T+3}{6(T+2)}.\]
5. **Constants/indices:** Offsets 3 and 2; denominator 6(T+2), always positive for natural T.
6. **Probability/feedback:** A moment of the next-bit parameter computed from length-T history, not a separately assumed stochastic variance model.
7. **Exclusions/boundaries:** T=0 gives 1/4, consistent with q([])=1/2. No T>0 premise or asymptotic replacement by 1/6.

## N11

1. **Objects:** Arbitrary deterministic A:List Bool->R, Boolean streams y,z and natural t.
2. **Quantifier order:** Every A,y,z,t, conditioned on equality of each strict-past entry.
3. **Assumptions:** \(\forall i<t,y_i=z_i\).
4. **Conclusion:** Predictions before the current target agree:
   \[\forall A,y,z,t,\quad(\forall i<t,y_i=z_i)\Rightarrow f5(A,y,t)=f5(A,z,t).\]
5. **Constants/indices:** A receives newest-first [y_{t-1},...,y_0]; no y_t. At t=0 receives [].
6. **Probability/feedback:** Actual deterministic strict-prefix invariance; not merely matching past predictions or a probability statement. A is fixed on both sides.
7. **Exclusions/boundaries:** No [0,1] bound on A needed. Current/future bits may differ. No claim about how external A was selected, computability, or stochastic independence.

## N12

1. **Objects:** Nonempty finite Boolean list h, chronological real indicator y=f4(h), n=length(h), mean m(y,n).
2. **Quantifier order:** Every h with n>0; conclusion first gives mean membership, then compares against EVERY u in [0,1].
3. **Assumptions:** n>0 only; the targets are automatically 0 or 1 by definition.
4. **Conclusion:** The hindsight mean is feasible and minimizes the displayed prefix squared loss over feasible comparators:
   \[\forall h,\ n>0\Rightarrow\left[m(y,n)\in[0,1]\land\forall u\in[0,1],\ \sum_{t=0}^{n-1}(m(y,n)-y_t)^2\le\sum_{t=0}^{n-1}(u-y_t)^2\right].\]
5. **Constants/indices:** One fixed full-prefix mean in every term; n terms, no half coefficient.
6. **Probability/feedback:** Hindsight comparison after the full sequence is specified; no assertion this comparator was available to A at earlier rounds.
7. **Exclusions/boundaries:** Empty h excluded in this target even though m(y,0)=0. No uniqueness or minimization over all ambient real u is explicitly asserted.

## N13

1. **Objects:** Any finite Boolean history h and arbitrary real prediction x.
2. **Quantifier order:** Every h,x, with no interval constraint on x.
3. **Assumptions:** None.
4. **Conclusion:** The two-point weighted squared loss is at least q(h)(1-q(h)):
   \[\forall h:\operatorname{List}(\mathrm{Bool}),\ \forall x\in\mathbb R,\quad q(h)(1-q(h))\le(1-q(h))x^2+q(h)(x-1)^2,\]
   Here h ranges over finite Boolean lists and x over all real scalars.
5. **Constants/indices:** Weights correspond to targets 0 and 1; no factor 1/2. Difference from the left is the square (x-q(h))^2.
6. **Probability/feedback:** A numerical two-outcome loss comparison for fixed h; it needs no random x or measurability hypothesis.
7. **Exclusions/boundaries:** Empty h allowed, x unbounded. It does not require x to equal q(h) or be generated by A; no sequence-level guarantee is assumed.

## N14

1. **Objects:** Arbitrary deterministic A:List Bool->R, positive natural T, actual f6 regrets and finite functional f7.
2. **Quantifier order:** For every A then every T>0, the weighted regret inequality is asserted.
3. **Assumptions:** T>0 only. A need not be bounded, measurable, or constrained to [0,1]. On each fixed length its relevant evaluations form a finite set.
4. **Conclusion:** Weighted signed regret to the SAME sequence's hindsight mean is bounded below:
   \[\forall A,T,\quad T>0\Rightarrow\frac{H_{T+1}}6\le f7(T,h\mapsto f6(A,h)).\]
5. **Constants/indices:** Harmonic index T+1, divisor 6, T-round regret at lists of length T. This is not H_T/6 or a logarithm yet.
6. **Probability/feedback:** The finite weighted average uses actual newest-first strict-past predictions f5(A,f3(h),t) inside f6; it is not an expectation over independently resampled predictions or an assumed universal regret bound.
7. **Exclusions/boundaries:** T=0 excluded: empty regret is zero whereas H_1/6=1/6. This is a weighted-average claim, not a statement that every list has that regret or that all individual regrets are nonnegative.

## N15

1. **Objects:** Arbitrary seed type Omega with measurable space, probability measure mu, map A:Omega->List Bool->R, and natural T.
2. **Quantifier order:** Universally choose Omega,mu,A with its conditions, then T>0; AFTER fixing this randomized learner and horizon, there exists ONE length-T Boolean vector v, followed by an integral over omega. In particular v is outside the seed integral and does not vary with omega.
3. **Assumptions:** IsProbabilityMeasure(mu); for EVERY history h, omega->A(omega,h) is measurable; for EVERY omega,h, A(omega,h) in [0,1]; T>0. Pointwise boundedness is not merely almost-everywhere boundedness or boundedness only along one selected history.
4. **Conclusion:** One fixed target sequence has seed-averaged regret at least the harmonic quantity:
   \[\forall(\Omega,\mu,A),\quad[\mu(\Omega)=1\land(\forall h,\ A(\cdot,h)\text{ measurable})\land(\forall\omega,h,\ 0\le A(\omega,h)\le1)]\Rightarrow
   \forall T>0,\ \exists v:\operatorname{Vector}(\mathrm{Bool},T),\quad\frac{H_{T+1}}6\le\int_\Omega f6(A(\omega,\cdot),v.\mathrm{toList})\,d\mu(\omega).\]
5. **Constants/indices:** Same 1/6 harmonic constant and T+1 index. For each omega, f6 uses that seed's SAME deterministic strict-past prediction map and the fixed v's empirical-mean comparator.
6. **Probability/feedback:** Randomness is an arbitrary exogenous seed law; no particular seed distribution is chosen in the conclusion. A(omega,·) is fixed along each run. The fixed-sequence placement rules out picking a different adversarial sequence after observing each seed. No joint law or separately formalized independence predicate is included; the statement has the fixed-sequence/seed-integral structure, not conditioning on a random seed-dependent v.
7. **Exclusions/boundaries:** T=0 excluded; endpoints 0,1 allowed. No assertion that the bound holds for each seed, each list, or a universal list working for all A. The witness may depend on A,mu,T. No runtime finite-query, adversarial adaptivity, or external-construction independence certificate.

## N16

1. **Objects:** Same general seed space, probability mu, measurable bounded family A, and positive natural horizon T as N15.
2. **Quantifier order:** For every such randomized learner and every positive T, there exists a fixed v outside the seed integral. It is not forall omega exists v or a single v universally chosen before A.
3. **Assumptions:** Same probability, per-history measurability, pointwise all-seed/all-history [0,1] boundedness, and T>0. No further stochastic law.
4. **Conclusion:** Some fixed length-T sequence has seed-averaged regret at least the logarithmic expression:
   \[\forall(\Omega,\mu,A),\quad[\mu\text{ probability}\land(\forall h,A(\cdot,h)\text{ measurable})\land(\forall\omega,h,A(\omega,h)\in[0,1])]\Rightarrow
   \forall T>0,\ \exists v:\operatorname{Vector}(\mathrm{Bool},T),\quad\frac{\log(T+2)}6\le\int_\Omega f6(A(\omega,\cdot),v.\mathrm{toList})\,d\mu(\omega).\]
5. **Constants/indices:** Natural logarithm of real-coerced T plus 2, divisor exactly 6; no subtraction, averaging by T, or asymptotic big-O notation.
6. **Probability/feedback:** Expected regret is over the learner seed only after a single target sequence is fixed. The actual strict-past trajectories and same hindsight comparator used by f6 remain unchanged.
7. **Exclusions/boundaries:** T=0 excluded (log 2/6 positive versus empty regret zero). No almost-sure, high-probability, per-seed, all-sequence, or one-witness-all-horizons guarantee. The target is a parameterized Prop, not a supplied proof of a logarithmic lower-bound theorem.

## Ambiguities and evidence boundary

No supplied-definition ambiguity blocks reconstruction. The packet does not supply a joint distribution of seed and targets or a separate independence axiom; interpreting the seed as independent operational randomness must respect the precise fixed-vector-outside-integral quantifiers, not invent a joint-law premise. All statements above describe the typed targets; neither manifest claims nor imports establish their proofs. Source fidelity, proof validity, compilation, acceptance, and chapter/Goal completion are not assessed. Runtime settings remain unattested, and reused staged history is disclosed.