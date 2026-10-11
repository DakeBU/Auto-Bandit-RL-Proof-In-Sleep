# Neutral weighted-potential certificate reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and reasoning effort are not independently attested. This reused automated decoder has related staged history; the present source-withheld reading is not absolute blindness, fresh-history independence, human or external review. Only the designated neutral packet was read. Its theorem transcript ends at “:= by” without a proof body; no compilation or proof verification was performed.

## Complete natural-language statement

Let A and W be arbitrary real sequences indexed by natural numbers, B any real constant, and n a strictly positive natural number. Assume W is nonnegative at every index below n and nondecreasing between each adjacent pair whose upper index is still below n. Assume every A_t with t<n is at most B. Then the sum of the successive differences A_t−A_(t+1), each multiplied by W_t, is at most B times the last played weight W_(n−1), minus the terminal value A_n times that same last weight.

There is no bound on A_n among the premises, and no sign restriction on A or B. The terminal term is retained with its sign; it is not discarded.

## Exact quantified formula

\[
\begin{aligned}
&\forall A:\mathbb N\to\mathbb R,\
\forall W:\mathbb N\to\mathbb R,\
\forall B\in\mathbb R,\
\forall n\in\mathbb N,\\
&0<n\ \Longrightarrow\
[\forall t\in\mathbb N,\ t<n\Rightarrow 0\le W_t]\ \Longrightarrow\\
&[\forall t\in\mathbb N,\ t+1<n\Rightarrow W_t\le W_{t+1}]\ \Longrightarrow\\
&[\forall t\in\mathbb N,\ t<n\Rightarrow A_t\le B]\ \Longrightarrow\\
&\sum_{t=0}^{n-1}(A_t-A_{t+1})W_t
\le B\,W_{n-1}-A_nW_{n-1}.
\end{aligned}
\]
All operations are real except the natural indices, their comparisons and n−1. The bound can also be written (B−A_n)W_(n−1), but the displayed two-term form preserves the exact endpoint subtraction.

## Seven semantic slots

1. **Model:** Two arbitrary deterministic real sequences A,W, a real scalar B and a positive finite natural horizon n. There is no implicit vector type, norm, probability space or algorithmic state. “Potential” and “weight” are explanatory labels only.

2. **Objective:** Upper-bound a finite weighted sum of successive potential differences. The expression is not defined as regret, energy, loss, expectation or a time average. B is a supplied upper bound on the preterminal A values, not necessarily their maximum or a positive constant.

3. **Hypotheses:** hT is 0<n. hw is ∀t<n,0≤W_t. hM is ∀t,t+1<n→W_t≤W_(t+1). hB is ∀t<n,A_t≤B. No A_t≥0, B≥0, A_n≤B, A_n≥0, strict weight positivity, strict monotonicity, or lower bound on A appears. There is no condition on W_n or later weights.

4. **Quantifiers and order:** Universal A then W (the grouped Lean binder A W), followed by B,n,hT,hw,hM,hB. The inner t quantifiers occur separately in the three hypotheses. range n is exactly 0,…,n−1, so the final summand uses A_(n−1)−A_n and W_(n−1). The bound hB includes A0 through A_(n−1), excluding A_n.

5. **Algorithm-information:** No feedback or causal-selection model is specified. Each summand involves the next sequence value A_(t+1), so it is not an expression using only indices through t. W may have been selected by any external mechanism; the type imposes only the displayed finite-prefix algebraic constraints. Terms A beyond n and W at or beyond n do not appear.

6. **Conclusion, signs and boundary cases:** The right side has +B W_(n−1) and −A_n W_(n−1), with no normalization, reciprocal or factor 1/2. Both sides may be negative. Since A_n is unconstrained, replacing the right side by B W_(n−1) would require an additional sign condition that is absent. At n=1 the adjacent-monotonicity premise is vacuous, and the asserted inequality reads (A0−A1)W0≤(B−A1)W0 with A0≤B and W0≥0. n=0 is explicitly excluded, despite Lean's total natural subtraction; there is no empty-horizon claim here. Zero weights are allowed. If all first n weights are zero, both sides are zero regardless of A_n. If W_(n−1)=0, the nonnegative/nondecreasing prefix conditions force the played weights to be zero. Constant weights, negative B, and negative A values are allowed when the written inequalities hold. No zero-denominator issue occurs because no division appears.

7. **Evidence and excluded claims:** This is one proposed implication with its complete premises. The packet supplies no theorem body, so it does not establish the certificate, a telescoping proof, algorithmic performance, or source correspondence. The statement does not produce sequences, guarantee its assumptions, constrain the terminal A_n, or assert a lower bound/equality. No unresolved type or semantic ambiguity was identified.

## Status

The single complete proposition is reconstructed with all quantifiers, exact endpoints, seven slots and degeneracies. The original bytes are preserved and checked before/after. No other input was consulted and no proof, compilation, source-matching or acceptance claim is made.
