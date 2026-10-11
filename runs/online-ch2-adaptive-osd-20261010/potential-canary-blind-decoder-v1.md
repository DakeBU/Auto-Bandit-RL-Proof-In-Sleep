# Two neutral weighted-potential canary reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium, with no independent runtime model/effort attestation. This reused automated decoder has related staged history. This is source-isolated for the present input, not absolute blindness, fresh-history independence, human or external review. Only the specified neutral file was read. No source, production body, design explanation or reviewer output was consulted. The two theorem headers supply no proof bodies; no compilation or proof acceptance is claimed.

## Four complete concrete sequences

All sequences have domain N and codomain R:
\[
P_0=3,\ P_1=1,\ P_2=3,\ P_3=2,\quad P_t=1\ (t\ge4);
\]
\[
W_0=0,\ W_1=1,\ W_2=1,\quad W_t=2\ (t\ge3);
\]
\[
Q_0=-3,\ Q_1=-2,\ Q_2=-4,\quad Q_t=7\ (t\ge3);
\]
\[
Z_0=0,\quad Z_t=5\ (t\ge1).
\]
These are fixed definitions, not free parameter sequences. All sums use natural indices, exclude the upper endpoint, and take real values. No random, algorithmic or probabilistic structure is defined.

## certificate_one

Write
\[
S=\sum_{t=0}^{3}(P_t-P_{t+1})W_t,\qquad
H=4W_3-P_4W_3.
\]
The seven conjuncts assert S≤H, S=1, terminal product P4W3=2, strict S<H, a zero first weight, equal weights at indices 1 and 2, and an increase of P from index 1 to 2.

\[
S\le H\ \land\ S=1\ \land\ P_4W_3=2\ \land\
S<H\ \land\ W_0=0\ \land\ W_1=W_2\ \land\ P_1<P_2.
\]

1. **Objects/model:** The actual fixed sequences P,W, horizon 4, scalar upper-bound coefficient 4, weighted difference sum S and endpoint expression H.
2. **Quantifiers/objective:** Closed seven-part conjunction, with only t bound in the finite sums. It compares weighted successive differences to the specified endpoint expression, not to an arbitrary B or arbitrary horizon.
3. **Hypotheses:** No external premises. Neither weight conditions nor a bound on P is assumed by a theorem argument here; all named functions are concrete, and the listed relations are asserted conclusions.
4. **Conclusion:** All seven assertions are retained, including both non-strict and strict comparisons. The terminal contribution is explicitly P4W3=2 and enters H with a minus sign.
5. **Constants/indices/boundaries:** range 4={0,1,2,3}; the last summand uses P3−P4 with W3. P4=1 and W3=2, so the displayed RHS is 8−2=6. The type separately asserts S=1 and strict comparison to this RHS. The first weight is zero, the middle weights may tie, and the potential has an increase 1<3 between P1,P2. No denominator or zero-division convention is needed. W4 is not used.
6. **Information:** Static finite arithmetic; t-th terms refer to the next potential P_(t+1). No pre-observation choice rule or causal algorithm is specified. The sequences' definitions beyond the used indices do not introduce an all-horizon conclusion.
7. **Evidence/excluded scope:** Does not require strictly increasing weights or nonincreasing potential, as its explicit equality/increase clauses show. Does not assert equality S=H, a universal bound for all sequences, regret, or performance. The header does not prove its numeric equalities or inequalities.

## certificate_two

There are four conjuncts comprising two different tests. First, for the fixed Q prefix of length 3, every multiplier is the literal real zero and the comparator coefficient is −2. Second, the length-1 Z prefix has constant weight 2 and comparator coefficient 1. Its sum is asserted to be −10 and its endpoint expression −8.

Define, for exposition only,
\[
S_Q=\sum_{t=0}^{2}(Q_t-Q_{t+1})\,0,\qquad
H_Q=(-2)\,0-Q_3\,0,
\]
\[
S_Z=\sum_{t=0}^{0}(Z_t-Z_{t+1})\,2,\qquad
H_Z=1\cdot2-Z_1\cdot2.
\]
Then the complete proposition is
\[
S_Q\le H_Q\ \land\ S_Z\le H_Z\
\land S_Z=-10\ \land H_Z=-8.
\]

1. **Objects/model:** Two fixed sequences Q,Z and two distinct finite horizons/scales. The zero weights in the first clause and weight 2 in the second are literal constants; the previously defined W is not used in this theorem.
2. **Quantifiers/objective:** Closed four-part conjunction. Each finite sum binds its own natural t. No universal potential, coefficient, weight or horizon quantifier occurs.
3. **Hypotheses:** No external assumptions. In the Q case the preterminal values −3,−2,−4 are at most the displayed coefficient −2, while terminal Q3=7 is not; in the Z case initial Z0=0 is at most 1, while terminal Z1=5 is not. These observations describe the fixed definitions, not additional premises of the type.
4. **Conclusion:** The zero-weight inequality; the signed single-step inequality; exact negative sum −10; and exact negative RHS −8. Both last equalities refer to the Z test, not to Q.
5. **Constants/indices/boundaries:** The Q sum is nonempty, with t=0,1,2 and terminal Q3. Zero weights make both S_Q and H_Q zero despite the negative preterminal coefficient and positive unconstrained terminal. This is not a zero-horizon case. The Z sum has only t=0, involving Z0−Z1 and weight 2. Its endpoint term is −Z1·2=−10, while the leading term is 2, producing −8. Both sides of that comparison are negative; the type asserts ≤ rather than a separate strict inequality. No horizon-zero assertion occurs anywhere in these two headers.
6. **Information:** No algorithm or probability. A horizon of 1 contains no adjacent pair of played weights to compare; the second clause does not assert such a monotonicity premise. The terminal potential can exceed the preterminal bound, and its negative product is explicitly retained.
7. **Evidence/excluded scope:** Does not impose global nonnegativity of the potential or coefficient, does not assert the terminal value is bounded by the coefficient, and does not license deletion of the terminal term. It does not prove a general zero-weight or one-step theorem. No supplied theorem body establishes these four assertions.

## Completeness and findings

Both entire conjunctions and all four sequence definitions are reconstructed: seven conjuncts in certificate_one and four in certificate_two. No unresolved mathematical/type ambiguity was identified. The first example includes zero and tied weights and a rising potential; the second separates nonempty all-zero weighting from a genuinely negative one-step sum and negative endpoint bound. Neither uses a zero horizon, and neither constrains terminal potentials by the displayed preterminal coefficient.

Only type semantics were assessed. No proof, source correspondence, compilation, publication or Goal-completion verdict is given.
