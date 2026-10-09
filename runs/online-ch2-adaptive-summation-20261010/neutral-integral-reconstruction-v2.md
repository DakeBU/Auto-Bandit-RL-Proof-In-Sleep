# Neutral integral-bound proposition reconstruction v2

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and reasoning effort are not independently attested. This reused automated decoder has related staged history; no absolute blindness, fresh-history independence, human or external review is claimed. Only the specified neutral Lean packet was read. It contains a #check proposition, not a supplied proof body. No proof, compilation, source identification or acceptance is assessed.

## Natural-language reconstruction

Take any nonnegative real starting point b, any real increment sequence d, any real function q defined on the whole real line, and any natural finite horizon N. Assume every increment with index below N is nonnegative, q is continuous and nonincreasing on the entire nonnegative half-line, and q is nonnegative throughout that half-line. Then the sum of each increment multiplied by q evaluated at the cumulative endpoint after that increment is at most the integral of q from b to the final cumulative endpoint.

Define
\[
s_0=b,\qquad s_k=b+\sum_{i=0}^{k-1}d_i.
\]
The proposed conclusion is
\[
\sum_{t=0}^{N-1}d_t q(s_{t+1})
\le \int_{b}^{s_N}q(x)\,dx.
\]
Thus q is sampled at the right endpoint of each increment interval, not at its left endpoint.

## Full quantifiers and assumptions

\[
\begin{aligned}
&\forall b\in\mathbb R,\ \forall d:\mathbb N\to\mathbb R,\
\forall q:\mathbb R\to\mathbb R,\ \forall N\in\mathbb N,\\
&b\ge0\ \Longrightarrow\
[\forall t\in\mathbb N,\ t<N\Rightarrow d_t\ge0]\ \Longrightarrow\\
&\operatorname{ContinuousOn}(q,[0,\infty))\ \Longrightarrow\
[\forall x,y\in[0,\infty),\ x\le y\Rightarrow q(y)\le q(x)]\ \Longrightarrow\\
&[\forall x\in[0,\infty),\ q(x)\ge0]\ \Longrightarrow\\
&\sum_{t=0}^{N-1}d_t\,q\!\left(b+\sum_{i=0}^{t}d_i\right)
\le
\int_b^{\,b+\sum_{i=0}^{N-1}d_i}q(x)\,dx.
\end{aligned}
\]
The unqualified interval integral notation uses the real volume measure, i.e. Lebesgue integration over the oriented real interval. It is not an expectation under a probability law.

## Seven semantic slots

1. **Objects and domains:** b is real, d is a natural-indexed real sequence, q is a total real-to-real function and N is natural. The regularity domain is Set.Ici 0=[0,∞). The finite sums take real values. No vector space, learner, action set, comparator or random variable occurs.

2. **Quantifier and implication order:** The universal binders are b,d,q,N in that order, followed by five successive hypotheses: nonnegative b; all played increments nonnegative; continuity on the half-line; antitonicity on the half-line; and pointwise nonnegativity there. All these are premises of the inequality, not conclusions or existentially selected objects. There is no uniform-in-N loss sequence construction or choice of q in the conclusion.

3. **Assumptions and regularity:** Only t<N increments are constrained. AntitoneOn means q(y)≤q(x) whenever 0≤x≤y, allowing constant segments. ContinuousOn means continuity relative to the half-line, including right-sided continuity at zero; it does not require continuity from negative arguments at zero. q need not be differentiable, strictly decreasing, strictly positive or bounded on the entire unbounded half-line by an independently supplied constant. No explicit integrability hypothesis is written; continuity on the relevant finite interval is the supplied regularity condition. All stated assumptions are retained even if some could be weakened in another theorem.

4. **Conclusion and exact normalization:** The bound compares a finite weighted right-endpoint sum with one integral:
\[
\sum_{t<N}d_t q(s_{t+1})\le\int_b^{s_N}q.
\]
There is no division by N, no averaging, no extra initial term, no 1/2 coefficient, and no replacement of q(s_(t+1)) by q(s_t). The weight is the actual increment d_t, not a step-size reciprocal or a difference in q.

5. **Constants, indices and zero cases:** range N means 0,…,N−1; the inner range(t+1) includes the current d_t. At N=0 the increment hypothesis is vacuous, the outer sum is zero and both integral endpoints are b, so the displayed conclusion is 0≤0. The three q premises and b≥0 remain in the type even then. Zero increments are allowed and repeat an endpoint while contributing zero. If all first N increments vanish, both sides have zero interval/weighted sum. b=0 and q≡0 are allowed. The nonnegative increments make s0,…,sN nondecreasing and keep them in [0,∞); no strictly positive interval length is required. There is no denominator or singular power in the proposition.

6. **Information and ambient-extension semantics:** This is deterministic finite-prefix analysis. The t-th summand uses d0,…,d_t, so it includes the current increment; increments at index N or later do not enter either side. q is defined on all R, but hypotheses constrain it only on [0,∞) and the asserted expressions evaluate/integrate it only on the nonnegative interval [b,sN]. Its behavior on negative inputs is unrestricted by this type; no global continuity or monotonicity may be inferred. Conversely, the assumptions concern the entire nonnegative half-line, not merely [b,sN]. There is no probability, filtration, feedback protocol or causal learner assertion.

7. **Boundary of the claim and unresolved questions:** The statement has no conclusion for negative b or a negative increment among the first N, and does not assert equality, a converse, a sharp constant or a general bound for an increasing q. Oriented interval integration is well-defined in Lean more generally, but these premises fix endpoint order b≤sN. The endpoint/zero cases above explain the type rather than supply a proof. The #check directive does not establish the proposition's truth or indicate compilation was performed. No unresolved type or semantic ambiguity was identified.

## Completion

One complete proposition has been reconstructed in prose, full quantified LaTeX and seven slots. The exact input bytes were bound before and after. No source was sought and no input, production code or proof was changed.
