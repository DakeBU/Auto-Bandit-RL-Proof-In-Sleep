# Two neutral summation canary reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium, without independent runtime model/effort attestation. This automated actor has reused related staged history; no absolute blindness, fresh-history independence, human or external review is claimed. Only the specified neutral input was read. Both expressions are #check propositions without theorem bodies. This report interprets their assertions, not their truth; no proof or compilation was performed.

## Proposition 1: nonconstant integrand with one zero increment

For notation only, abbreviate the functions actually repeated in the type by
\[
d_t=\begin{cases}0&t=1\\1/2&t\ne1,\end{cases}
\qquad q(x)=\max(1-x,0),\qquad
s_k=0+\sum_{i<k}d_i.
\]
Set
\[
S=\sum_{t<3}d_tq(s_{t+1}),\qquad J=\int_0^{s_3}q(x)\,dx.
\]
The proposition has eight top-level conjuncts: S≤J, S=1/4, J=1/2, S<J, q(0)≠q(1), d0=1/2, d1=0 and d2=1/2. In words, the concrete weighted right-endpoint sum is bounded by the integral, their asserted exact values make the comparison strict, the integrand is not constant between the tested points, and the three increment values include a zero middle increment.

\[
S\le J\ \land\ S=\tfrac14\ \land\ J=\tfrac12
\ \land\ S<J\ \land\ q(0)\ne q(1)
\ \land\ d_0=\tfrac12\ \land\ d_1=0\ \land\ d_2=\tfrac12.
\]

1. **Objects:** A concrete real integrand q, natural-indexed real increment function d, starting point 0, horizon 3, one weighted finite sum and one real interval integral.
2. **Quantifiers/order:** Closed eight-part conjunction. t and i are bound finite-sum indices; x is the integral/function argument. The notational abbreviations above introduce no extra universal or existential parameters.
3. **Assumptions:** No external hypotheses. Sum and integral values, both comparisons, nonconstancy and increment identities are proposed conclusions. No general regularity theorem is a premise of this type.
4. **Conclusion:** All eight clauses are retained, including both ≤ and <. The integral and sum in each repeated clause are exactly the same S and J, not quantities with different endpoints or index sets.
5. **Constants/indices/boundaries:** range 3 is {0,1,2}; inner range(t+1) includes the current d_t. The successive right endpoints are s1=1/2,s2=1/2,s3=1. Thus both the final cumulative endpoint and upper integral endpoint are 1; the repeated endpoint comes from d1=0. The sum samples q after each increment and weights by that same increment. The final term samples the truncation boundary x=1. Values d_t at t≥3 are defined by the formula but not used here.
6. **Information/integration:** Deterministic finite-prefix expression; no probability or online feedback protocol. Integration is the real interval integral with the default real volume measure. q is an ambient real function, with truncation max(1−x,0), not a function restricted in type to [0,1]. The explicit inequality q(0)≠q(1) rules out constancy at those points without asserting strict decrease on all R.
7. **Excluded scope:** This is not a general claim for every sequence, integrand or horizon, and does not assert that a zero increment prevents strictness. Exact asserted arithmetic values are not proof evidence; no derivative, global strict monotonicity or numerical integration procedure is supplied.

## Proposition 2: empty horizon versus all-zero increments

Abbreviate the concrete ambient function h(x)=max(3−x,0). The proposition has three conjuncts. First, at starting point 2 and horizon zero, the sum with unit increments is at most the integral to its empty cumulative endpoint. Second, at starting point 2 and horizon three, the sum with all increments zero is at most the integral to its unchanged cumulative endpoint. Third, h(2)=1.

\[
\begin{aligned}
&\left[\sum_{t<0}1\cdot h\!\left(2+\sum_{i<t+1}1\right)
\le\int_2^{\,2+\sum_{i<0}1}h(x)\,dx\right]\\
&\land\left[\sum_{t<3}0\cdot h\!\left(2+\sum_{i<t+1}0\right)
\le\int_2^{\,2+\sum_{i<3}0}h(x)\,dx\right]
\land h(2)=1.
\end{aligned}
\]

1. **Objects:** Same fixed real function h in both inequalities, initial location 2, two separate increment/horizon cases, and its value at 2.
2. **Quantifiers/order:** Three closed conjuncts. Sum indices are natural and bound, with no universally quantified increment stream or horizon.
3. **Assumptions:** None external. Neither inequality nor h(2)=1 is assumed beforehand.
4. **Conclusion:** Two non-strict inequalities and one exact nonzero function value. No strict inequality appears in this proposition.
5. **Constants/indices/boundaries:** In the first clause the outer range 0 is empty despite the displayed increments being 1; there is no evaluated time step. Its integral endpoints are both 2. In the second clause range 3 has three entries, but each weight is 0 and every inner cumulative increment is zero; its right endpoints and integral endpoint are all 2. Both comparisons therefore have the zero-sum/zero-length form 0≤0 as a semantic simplification. This is not the same index structure: empty horizon and nonempty horizon with zero increments are distinct cases.
6. **Information/integration:** Real deterministic interval integrals, not expectations. The zero results arise from empty sums or zero weights and repeated endpoints, not from a zero integrand: the third clause expressly gives h(2)=1. No value at a future time or probabilistic event is involved.
7. **Excluded scope:** Does not assert h vanishes at 2 or that its integral over any positive-length interval is zero. The first clause does not test a unit-increment step at t=0 because no such outer index exists. No all-horizon generalization, proof or compilation result is supplied.

## Completeness and status

Both complete propositions have natural-language, exact formula and seven-slot reconstructions, with eight and three conjuncts respectively. No unresolved type or semantic ambiguity was identified. The scalar abbreviations are expository expansions of the supplied expressions only, not changes to the inputs or proposed statements. No source material, contract, other reconstruction or proof was read. The input's raw hash was checked before and after.
