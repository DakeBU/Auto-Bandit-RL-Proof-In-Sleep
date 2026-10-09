# Nine finite-selector terminal reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and reasoning effort are not independently attested. This actor is distinct from the assigning formalizer/source-review role but has related staged task history. This is a source-identity-withheld packet reconstruction, not absolute contextual blindness, human review or external independence. Only the specified neutral Lean file was read.

The nine #check expressions describe propositions. They do not supply inhabitants or proofs of those propositions; no compilation was run. The report neither identifies a mathematical source nor judges production-code fidelity.

## Four complete definitions

X is an arbitrary type, and n is an arbitrary natural number. No order, topology, vector structure, finiteness or inhabited instance on X is assumed.

For past:Fin n→X→R, define
\[
C_{\mathrm{past}}(x)=\sum_{i\in\operatorname{Fin}(n)}\mathrm{past}_i(x),
\qquad
M(V,\mathrm{past})=\{x:x\in V\land
\forall y\in V,\ C_{\mathrm{past}}(x)\le C_{\mathrm{past}}(y)\}.
\]
IsMinOn is the latter value comparison; membership is separately included in M. Finite n means a finite history, not a finite feasible domain. A real-valued cumulative loss need not attain a minimum on an arbitrary nonempty V.

S(V,past) is some(Classical.choose h) when h states M is nonempty, and none otherwise. It is a noncomputable choice based on the minimizer set. Ties are allowed; no order-based tie-breaker, uniqueness, randomness or efficient algorithm is specified.

P takes initial:V, a subtype element that contains both its value in X and proof of feasibility:
\[
P(V,\mathrm{initial},\mathrm{loss},t)=
\begin{cases}
\mathrm{some}(\mathrm{initial}:X),&t=0,\\
S(V,(i\mapsto\mathrm{loss}_{i.\mathrm{val}})_{i\in\operatorname{Fin}(t)}),&t>0.
\end{cases}
\]
This is a direct finite-prefix rule, not a recursive Option.bind algorithm. A none at one time does not by definition force none at later times. At t>0 the initial value does not occur in the branch, but at t=0 it is explicitly returned rather than an arbitrary minimizer selected by S. No regret or score function is defined.

Empty V is allowed for C/M/S, but no initial:V exists in that case. For n=0 the cumulative objective is zero everywhere, so M(V,empty)=V: S has a feasible choice iff V is nonempty. For P, the feasible initial always makes the zero-horizon objective attained. X itself may be empty in the generic context; a p or initial argument then cannot be supplied.

## Terminal 1

For every loss stream, natural t and point x, summing its finite prefix over Fin t equals summing over the natural range below t.
\[
\forall\ell:\mathbb N\to X\to\mathbb R,\ \forall t\in\mathbb N,\ \forall x\in X,\quad
C_{i\mapsto\ell_{i.\mathrm{val}}}(x)=\sum_{i=0}^{t-1}\ell_i(x).
\]

1. **Objects:** Arbitrary X, real loss stream, finite prefix and point x.
2. **Quantifiers/order:** loss,t,x; no hypotheses.
3. **Assumptions:** Only the displayed types.
4. **Conclusion:** Exact equality between two representations of the same finite sum.
5. **Constants/indices:** Fin t corresponds to 0,…,t−1; t=0 yields empty sums equal to zero.
6. **Information:** No loss at index t or later appears.
7. **Boundary/scope:** No minimizer, feasibility or prediction claim, and no proof is supplied by #check.

## Terminal 2

If S returns some p, that p is feasible and minimizes the cumulative history loss on V.
\[
S(V,h)=\mathrm{some}(p)\Rightarrow
p\in V\land\forall y\in V,\ C_h(p)\le C_h(y).
\]

1. **Objects:** Arbitrary X,n,V,past h and returned p.
2. **Quantifiers/order:** V,h,p,then success equality.
3. **Assumptions:** Only S(V,h)=some p; no uniqueness or explicit existence premise.
4. **Conclusion:** Feasibility and IsMinOn jointly.
5. **Constants/indices:** Any n, including n=0; then the selected p is any selected feasible point among constant-objective ties.
6. **Information:** This specifies the actual chosen result, not an arbitrary minimizer.
7. **Boundary/scope:** Empty V cannot meet the success premise. Does not say every minimizer is the chosen p.

## Terminal 3

S is none exactly when there is no feasible minimizer.
\[
S(V,h)=\mathrm{none}\Longleftrightarrow
\neg\exists p\in X,\ p\in V\land\operatorname{IsMinOn}(C_h,V,p).
\]

1. **Objects:** Arbitrary X,n,V and finite history h.
2. **Quantifiers/order:** Universal V,h followed by an iff and negated existential p.
3. **Assumptions:** None.
4. **Conclusion:** Exact mathematical failure/nonattainment equivalence.
5. **Constants/indices:** n=0 reduces the existential to nonempty V. Positive finite history does not imply attainment.
6. **Information:** none signifies lack of a minimum in the defined choice rule, not timeout or an unknown answer.
7. **Boundary/scope:** Nonempty V may lack a minimum; ties do not cause none. No attainment theorem is asserted.

## Terminal 4

If each pair of corresponding historical losses agrees on V, their selectors agree, even if the losses differ outside V.
\[
[\forall i\in\operatorname{Fin}(n),\ \forall z\in V,\ h_i(z)=h'_i(z)]
\Rightarrow S(V,h)=S(V,h').
\]

1. **Objects:** Same V and same history length n, with two histories.
2. **Quantifiers/order:** V,h,h',then every-index EqOn premise.
3. **Assumptions:** Pointwise agreement on V only; global equality of functions is not required.
4. **Conclusion:** Exact Option equality, including the chosen point if successful, not just equality of attained minimum values.
5. **Constants/indices:** For n=0 the premise is vacuous. Empty V also makes it vacuous and both selectors have no feasible witness.
6. **Information:** The selected object is determined via the minimizer set, so the target asserts invariance under outside-domain changes. No uniqueness premise appears; tied histories are included.
7. **Boundary/scope:** This is a property of this extensional set-based S, not a theorem about every arbitrary tie-breaking policy. No proof of that invariance was supplied.

## Terminal 5

Given a feasible minimizer p that is the only feasible minimizer, S returns exactly some p.
\[
p\in V\land\operatorname{IsMinOn}(C_h,V,p)
\land[\forall q\in V,\operatorname{IsMinOn}(C_h,V,q)\Rightarrow q=p]
\Rightarrow S(V,h)=\mathrm{some}(p).
\]

1. **Objects:** V,h,p and all candidate feasible minimizers q.
2. **Quantifiers/order:** V,h,p,hp,hmin,hunique; the uniqueness quantifier is inside hunique.
3. **Assumptions:** Membership, global-over-V minimality, and uniqueness within V are separate premises.
4. **Conclusion:** Exact actual selector identity.
5. **Constants/indices:** At n=0 every feasible point minimizes; uniqueness requires V have no other point than p.
6. **Information:** p is supplied, not constructed by the theorem's conclusion.
7. **Boundary/scope:** Without uniqueness this header does not assert S picks a specified member of a tie. No uniqueness outside V is assumed.

## Terminal 6

For every feasible initial subtype element and loss stream, P at time zero returns that exact initial value.
\[
P(V,\mathrm{initial},\ell,0)=\mathrm{some}((\mathrm{initial}:X)).
\]

1. **Objects:** V, initial:V, loss:N→X→R.
2. **Quantifiers/order:** V,initial,loss, all universal.
3. **Assumptions:** Feasibility is carried by the subtype; no separate hp binder.
4. **Conclusion:** Exact zero-time value.
5. **Constants/indices:** Horizon/time 0; no observations used. It need not equal the separate arbitrary S(V,empty) choice.
6. **Information:** Initial prediction ignores the entire loss stream.
7. **Boundary/scope:** Empty V has no initial argument, so this is not an existence assertion for an empty domain.

## Terminal 7

If P at t returns p, then p is feasible and minimizes the strict-prefix loss sum through t−1.
\[
P(V,\mathrm{initial},\ell,t)=\mathrm{some}(p)\Rightarrow
p\in V\land\operatorname{IsMinOn}
\left(z\mapsto\sum_{i<t}\ell_i(z),V,p\right).
\]

1. **Objects:** Actual P, feasible initial, arbitrary loss stream,t and p.
2. **Quantifiers/order:** V,initial,loss,t,p,then success premise.
3. **Assumptions:** P success only, beyond the subtype.
4. **Conclusion:** Membership and exact finite-prefix minimum.
5. **Constants/indices:** Includes t=0: the initial is feasible and all feasible points minimize the zero sum. For t>0 the minimum uses exactly t losses.
6. **Information:** Current loss at t is excluded; no post-current update is scored or defined.
7. **Boundary/scope:** No success for every t is guaranteed. The conclusion does not assert a unique minimizer or global ambient minimum.

## Terminal 8

P at t is none exactly when the cumulative prefix has no feasible minimizer.
\[
P(V,\mathrm{initial},\ell,t)=\mathrm{none}\Longleftrightarrow
\neg\exists p,\ p\in V\land
\operatorname{IsMinOn}\left(z\mapsto\sum_{i<t}\ell_i(z),V,p\right).
\]

1. **Objects:** V with supplied subtype initial,loss and natural t.
2. **Quantifiers/order:** V,initial,loss,t,then iff with negated existential.
3. **Assumptions:** Only types/subtype feasibility.
4. **Conclusion:** Failure equivalence for the actual direct-prefix P.
5. **Constants/indices:** At t=0 both sides are false: P is some initial and the zero objective has that feasible minimizer.
6. **Information:** Each t recomputes from its own prefix; the type says nothing about failure persistence.
7. **Boundary/scope:** Does not assert all nonempty domains attain every finite sum, or that finite history means a finite feasible set.

## Terminal 9

Two loss streams agreeing on V at all times strictly below t give the same P value at t, with the same feasible initial.
\[
[\forall s<t,\ \forall z\in V,\ \ell_s(z)=\ell'_s(z)]
\Rightarrow P(V,\mathrm{initial},\ell,t)
=P(V,\mathrm{initial},\ell',t).
\]

1. **Objects:** Same V,initial,t, and two entire real loss streams.
2. **Quantifiers/order:** V,initial,loss,loss',t,then strict-prefix EqOn premise.
3. **Assumptions:** Equality on V only for s<t, not global equality, not equality at t or any future index.
4. **Conclusion:** Exact Option equality, including the selected point through ties.
5. **Constants/indices:** t=0 makes the premise vacuous and both return the shared initial. No off-by-one current-loss condition.
6. **Information:** Finite strict-past information and no dependence on losses outside V or future loss coordinates under this comparison.
7. **Boundary/scope:** Shared initial is explicit. This is not a statement about different initial values at zero, arbitrary tie selectors, or loss histories of different lengths.

## Findings and completeness

All nine Terminal propositions have complete prose, formulas and seven slots. All four definitions were interpreted without adding structure to X. No type/semantic ambiguity was identified.

The strongest scope-sensitive assertion is Terminal 4/9's exact choice equality under EqOn despite ties. It is meaningful for the actual set-based Classical.choose definition; it is not interchangeable with arbitrary-policy invariance. Initialization uses the supplied feasible subtype, while positive-time selection ignores that value. An empty prefix is not an empty feasible set, and P's failure is not recursively absorbing. These are reconstructed meanings, not proved conclusions. The packet's #check probes cannot establish theorem truth or source acceptance.
