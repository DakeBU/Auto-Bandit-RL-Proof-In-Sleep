# Three neutral prefix-energy header reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and effort are not independently attested. This is a distinct reused automated decoder with related book/task history: source-withheld for this packet, not absolutely context-blind, human or externally independent. Only the designated neutral packet was read. No source, contract, proof body or reviewer material was consulted.

The three transcripts terminate at “:= by” without a body. They are proposed header-only statements, not completed theorem declarations or compilation evidence. This report reconstructs their mathematical content and does not prove them.

## Shared notation and total operations

For a real sequence b put
\[
B_k=\sum_{i=0}^{k-1}b_i.
\]
Thus the t-th denominator is sqrt(B_(t+1)), which includes the current b_t, and the final right side uses B_n. Finset.range n means the natural indices 0,…,n−1. Real.sqrt is the nonnegative real square-root operation (totalized to zero on negative inputs), and real division is totalized: a/0=0. The stated nonnegativity hypotheses ensure all prefix sums actually used are nonnegative.

For vectors in a normed additive commutative group put
\[
A_k=\sum_{i=0}^{k-1}\|v_i\|^2.
\]
No initial positive offset or epsilon appears in any denominator. Consequently leading zero increments and all-zero prefixes are included, with 0/0 interpreted as zero rather than undefined.

## 1. prefix_bound

For every natural-indexed real sequence b and finite horizon n, if its first n entries are nonnegative, then the sum of each entry divided by the square root of the cumulative sum through that entry is at most twice the square root of the final cumulative sum.
\[
\forall b:\mathbb N\to\mathbb R,\ \forall n\in\mathbb N,\quad
[\forall t<n,\ b_t\ge0]\Longrightarrow
\sum_{t=0}^{n-1}\frac{b_t}{\sqrt{B_{t+1}}}
\le2\sqrt{B_n}.
\]

1. **Model:** A deterministic scalar sequence and a finite natural horizon. No probability space or learner is present.
2. **Objective:** Bound the displayed finite normalized sum; it is not defined as loss, regret, risk or runtime.
3. **Hypotheses:** Only b_t≥0 for every t<n. No assumption is imposed on b at n or later, and no strict positivity or monotonicity is required.
4. **Quantifiers:** b and n are universally quantified, followed by hb. The inner sum index i ranges below t+1, while the outer t ranges below n. There are no hidden typeclass variables.
5. **Algorithm-information:** No algorithm is defined. The t-th term uses b0,…,b_t, including the current entry, not only the strict past. The inequality by itself does not authorize interpreting its reciprocal denominator as a pre-observation step size.
6. **Conclusion and boundaries:** Exact factor 2, no averaging by n, no added initial energy. At n=0 both sums are empty and the conclusion is 0≤0; hb is vacuous. If B_(t+1)=0 under the hypotheses, the contributing entries, including b_t, are zero, so the corresponding quotient is 0/0=0. All-zero and initially-zero sequences are allowed. Later negative entries outside the first n do not affect the expression.
7. **Evidence and exclusions:** The header asserts this implication but supplies no proof. It does not state equality conditions, sharpness of 2, a claim for negative played entries, or any algorithmic performance guarantee. No unresolved semantic ambiguity was identified.

## 2. vector_bound

For any type E equipped with NormedAddCommGroup E, any vector sequence v and any natural horizon n, the sum of squared norms divided by the square root of their inclusive cumulative sum is bounded by twice the square root of total squared norm.
\[
\forall E\ [\operatorname{NormedAddCommGroup}(E)],\
\forall v:\mathbb N\to E,\ \forall n\in\mathbb N,\quad
\sum_{t=0}^{n-1}\frac{\|v_t\|^2}{\sqrt{A_{t+1}}}
\le2\sqrt{A_n}.
\]

1. **Model:** Arbitrary normed additive commutative group E; real norm values and a finite sequence prefix. E is implicit in the Lean binder, universally quantified.
2. **Objective:** Bound normalized squared-norm contributions. Calling them “energy” is only a notational description, not a supplied application.
3. **Hypotheses:** No explicit premise on v. Norm squares supply nonnegative real entries. No NormedSpace, inner product, finite dimension, completeness, nontriviality, gradient property or bounded norm is required.
4. **Quantifiers:** Implicit E and its typeclass first, then all v:N→E and n:N. The denominator includes v_t through range(t+1); the terminal sum includes precisely t<n.
5. **Algorithm-information:** v is an arbitrary supplied sequence, not necessarily an iterate, gradient or subgradient stream. There is no state recurrence, feedback rule or independence premise.
6. **Conclusion and boundaries:** The exact factor and inclusive denominators match the formula above. n=0 gives zero on both sides. Zero vectors and the trivial one-element normed group are permitted. A zero cumulative norm-square denominator forces the current norm square to be zero, giving a totalized zero quotient. There is no positive initialization constant.
7. **Evidence and exclusions:** This is a proposed unconditional sequence inequality in the stated structure, not a proof or a performance bound for any specified algorithm. No omitted inner-product assumption may be added from the vector notation. No unresolved context was identified.

## 3. scaled_bound

For the same general normed additive commutative group and vector sequence, and for any nonnegative real scale R, half that scale times the normalized squared-norm sum is at most R times the square root of total squared norm.
\[
\forall E\ [\operatorname{NormedAddCommGroup}(E)],\
\forall v:\mathbb N\to E,\ \forall n\in\mathbb N,\
\forall R\in\mathbb R,\quad R\ge0\Longrightarrow
\frac R2\left(\sum_{t=0}^{n-1}
\frac{\|v_t\|^2}{\sqrt{A_{t+1}}}\right)
\le R\sqrt{A_n}.
\]

1. **Model:** Same implicit E and norm structure, arbitrary v,n and a real scalar R.
2. **Objective:** A scalar rescaling of the displayed finite energy sum; the type does not define R as a radius, diameter or distance.
3. **Hypotheses:** Only hR:0≤R in addition to the normed group structure. Strict positivity is not required; R is not required to bound any object.
4. **Quantifiers:** Implicit E/typeclass, then v,n,R,hR. Parentheses matter: (R/2) multiplies the entire sum; the denominator inside each term remains sqrt(A_(t+1)).
5. **Algorithm-information:** No new algorithm or tuning procedure. R is a supplied scalar, with no independence or causal-selection restriction. The same v and n appear on both sides.
6. **Conclusion and boundaries:** Exact left prefactor R/2 and right prefactor R. R=0 gives 0≤0 for any supplied sequence/horizon. n=0 or an all-zero prefix also gives zero on both sides. Leading zero denominators retain the totalized convention. Negative R is excluded by the premise; no division by R occurs.
7. **Evidence and exclusions:** No theorem body is present and no derivation from the preceding headers is supplied. The proposition is not by itself a regret guarantee or evidence of an implemented adaptive method. No unresolved semantic ambiguity was identified.

## Completeness and status

All three complete proposition signatures have natural-language and LaTeX reconstructions with the requested seven slots: model, objective, hypotheses, quantifiers, algorithm-information, conclusion, evidence. No unresolved type or semantic ambiguity was found. The input's incomplete proof introducers are explicitly treated as transcripts, not completed Lean proofs. Source matching and compilation were not assessed.
