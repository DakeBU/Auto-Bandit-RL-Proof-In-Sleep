# Eight finite-selector canary propositions, v2

Actor /root/osd_blind; requested GPT-6 Astra / medium; runtime model and effort not independently attested. This reused automated decoder has related staged history. No absolute blindness, fresh-history independence, human or external review is claimed. Only the specified v2 neutral packet was read. The eight #check Prop expressions are propositions, not supplied theorem proofs; compilation was not run.

## Four generic definitions and seven concrete definitions

For arbitrary X and natural n,
\[
C_h(x)=\sum_{i\in\mathrm{Fin}(n)}h_i(x),\quad
M(V,h)=\{x:x\in V\land\forall y\in V,\ C_h(x)\le C_h(y)\}.
\]
S(V,h) is some of a Classical.choose element of M when M is nonempty, otherwise none. Ties are allowed; no numerical tie-breaker is specified. IsMinOn alone is a value comparison, while M includes membership separately.

For a subtype element a:V,
\[
P(V,a,\ell,t)=
\begin{cases}\mathrm{some}((a:X)),&t=0,\\
S(V,(i\mapsto\ell_{i.\mathrm{val}})_{i\in\mathrm{Fin}(t)}),&t>0.
\end{cases}
\]
This is direct selection on a strict finite prefix, not a state recursion with absorbing none.

The seven concrete definitions are:
\[
D=[0,1],\quad a=(3/4\in D),\quad b=(1/4\in D),
\]
\[
q_t(x)=\begin{cases}(x-1/4)^2&t=0\\(x-3/4)^2&t>0,\end{cases}
\quad
q^{c}_t(x)=\begin{cases}q_t(x)&t<2\\x+100&t\ge2,\end{cases}
\]
\[
q^{e}_t(x)=\begin{cases}q_t(x)&x\in D\\x+7&x\notin D,\end{cases}
\quad
r_t(x)=\begin{cases}x&t=0\\x^2-x&t>0.\end{cases}
\]
Here q^c denotes qChanged and q^e denotes qExtended. a,b include feasibility proofs, not merely scalar values. Generic definitions require no topological or finite-domain structure on X; the examples specialize to R.

## Proposition 1

The initial subtype value is 3/4. The first three outputs for q are some(3/4), some(1/4), some(1/2). The two latter points differ, q0 distinguishes 1/4 from 3/4, and every time in range 3 has a feasible selected prefix minimizer.
\[
\begin{aligned}
&(a:\mathbb R)=3/4
\land P(D,a,q,0)=\mathrm{some}(3/4)
\land P(D,a,q,1)=\mathrm{some}(1/4)\\
&\land P(D,a,q,2)=\mathrm{some}(1/2)
\land 1/4\ne1/2
\land q_0(1/4)\ne q_0(3/4)\\
&\land[\forall t\in\{0,1,2\},\exists p,\
P(D,a,q,t)=\mathrm{some}(p)\land p\in D
\land\operatorname{IsMinOn}(x\mapsto\sum_{i<t}q_i(x),D,p)].
\end{aligned}
\]

1. **Objects:** Fixed D,a,q and prefix-dependent P; real selected p.
2. **Quantifiers/order:** Seven top-level conjuncts; last clause has ∀t∈range 3 ∃p with three properties.
3. **Assumptions:** None external. Feasibility of a is encoded by its definition; the displayed outputs and minimum specifications are assertions.
4. **Conclusion:** Exact states, two explicit inequalities, and actual chosen-minimizer specification at all three tested times.
5. **Indices/boundaries:** Time 0 uses no loss. Time 1 minimizes q0, time 2 minimizes q0+q1. range 3 includes 0 and excludes 3. At time 0 every feasible point minimizes the empty sum; initialization picks a.
6. **Information:** q_t is not used at time t; current and future losses do not enter the prefix.
7. **Excluded scope:** No all-time claim or uniqueness predicate is explicitly conjoined. A named quadratic instance and an exact selected point do not constitute a supplied proof of uniqueness or selection.

## Proposition 2

The original and changed streams differ at times 2 and 3 at input zero, yet have equal time-2 predictions.
\[
q_2(0)\ne q^c_2(0)\land q_3(0)\ne q^c_3(0)
\land P(D,a,q,2)=P(D,a,q^c,2).
\]

1. **Objects:** Two fixed streams, common D and initial a.
2. **Quantifiers/order:** Three closed conjuncts; no universal time claim.
3. **Assumptions:** None.
4. **Conclusion:** Two pointwise differences plus exact Option equality.
5. **Indices/boundaries:** The unequal values occur at current index 2 and future index 3 relative to the prediction time 2; both are excluded from its prefix. The first two losses are unchanged by the definition.
6. **Information:** Demonstrates strict-prefix dependence, not global stream equality.
7. **Excluded scope:** Does not assert predictions remain equal at every later time, or that the functions agree at indices 2,3.

## Proposition 3

The point 2 is outside D; q0 and qExtended0 differ there, but all their losses agree on D. Both the two-loss selector and time-2 prediction agree.
\[
\begin{aligned}
&2\notin D\land q_0(2)\ne q^e_0(2)
\land[\forall t,\forall x\in D,\ q_t(x)=q^e_t(x)]\\
&\land S(D,(q_i)_{i\in\mathrm{Fin}(2)})
=S(D,(q^e_i)_{i\in\mathrm{Fin}(2)})
\land P(D,a,q,2)=P(D,a,q^e,2).
\end{aligned}
\]

1. **Objects:** Feasible-domain extension of each loss, actual set-based selector and prefix rule.
2. **Quantifiers/order:** Five top-level conjuncts; only the EqOn clause quantifies all natural t and feasible x.
3. **Assumptions:** None; domain agreement itself is asserted.
4. **Conclusion:** Outside difference coexists with exact choice equality on the same feasible set.
5. **Indices/boundaries:** Fin 2 means losses 0 and 1; endpoint 2 here is an outside spatial point in the first clauses, not a time variable.
6. **Information:** EqOn on D is sufficient in the asserted example; global equality of loss functions is explicitly not present.
7. **Excluded scope:** No equality outside D or arbitrary-selector-policy theorem. This concerns the actual S defined by the minimizer set.

## Proposition 4

Both distinct endpoints 0 and 1 are feasible minimizers of the zero one-loss objective. Nevertheless S returns some feasible minimizer, without specifying which tied point.
\[
\begin{aligned}
&0\in D\land1\in D\land0\ne1
\land\operatorname{IsMinOn}(C_{(0)},D,0)
\land\operatorname{IsMinOn}(C_{(0)},D,1)\\
&\land\exists p,\ S(D,(0)_{i\in\mathrm{Fin}(1)})=\mathrm{some}(p)
\land p\in D\land\operatorname{IsMinOn}(C_{(0)},D,p).
\end{aligned}
\]

1. **Objects:** One-entry history whose loss is identically zero, the two interval endpoints, selected p.
2. **Quantifiers/order:** Six top-level conjuncts; final existential p has three simultaneous properties.
3. **Assumptions:** None; no uniqueness condition.
4. **Conclusion:** Explicit nonunique minimizers and successful actual selection.
5. **Indices/boundaries:** History length is 1, not zero. Objective is constant because that one loss is zero.
6. **Information:** Classical choice can select any of the tied minimizers; the type does not reveal a tie-breaking value.
7. **Excluded scope:** Cannot conclude p=0, p=1, p=a or p=b. Ties do not mean failure.

## Proposition 5

The selector on an empty feasible set with the single square loss returns none.
\[
S(\varnothing,(x\mapsto x^2)_{i\in\mathrm{Fin}(1)})=\mathrm{none}.
\]

1. **Objects:** Empty subset of R and one quadratic loss.
2. **Quantifiers/order:** Closed equality.
3. **Assumptions:** None.
4. **Conclusion:** No selected feasible point.
5. **Indices/boundaries:** A globally minimized quadratic cannot provide membership in an empty feasible set. The prefix length is 1.
6. **Information:** Static selector failure; no P initial is supplied on the empty domain.
7. **Excluded scope:** Does not say the objective lacks an ambient minimum, or that P can be initialized in an empty subtype.

## Proposition 6

For the empty history on nonempty D, S returns some feasible point. But P at zero uses its supplied initial: a gives 3/4 and b gives 1/4, hence the outputs differ.
\[
\begin{aligned}
&[\exists p,\ S(D,\mathrm{emptyHistory})=\mathrm{some}(p)\land p\in D]\\
&\land P(D,a,q,0)=\mathrm{some}(3/4)
\land P(D,b,q,0)=\mathrm{some}(1/4)
\land P(D,a,q,0)\ne P(D,b,q,0).
\end{aligned}
\]

1. **Objects:** Fin 0 history eliminated by Fin.elim0, two feasible subtype initializations and same loss stream.
2. **Quantifiers/order:** Four top-level conjuncts; first is existential p.
3. **Assumptions:** None external; a,b already include membership.
4. **Conclusion:** Empty-history S success and differing prescribed P initial outputs.
5. **Indices/boundaries:** No elements of Fin 0 exist; cumulative objective is the empty sum zero. Empty history is not empty D.
6. **Information:** P at time zero does not call S or read q. The selected S point need not equal either initial.
7. **Excluded scope:** No dependence on initial at positive time is asserted. No specific S tie-break result is supplied.

## Proposition 7

The whole real line is nonempty, closed and convex, but selecting a minimizer of the single identity loss fails. P with initial zero succeeds at time zero and fails at time one for the constant identity-loss stream.
\[
\begin{aligned}
&\mathbb R\ne\varnothing\land\operatorname{IsClosed}(\mathbb R)
\land\operatorname{Convex}_{\mathbb R}(\mathbb R)\\
&\land S(\mathbb R,(x\mapsto x)_{i\in\mathrm{Fin}(1)})=\mathrm{none}\\
&\land P(\mathbb R,(0\in\mathbb R),(x\mapsto x)_t,0)=\mathrm{some}(0)\\
&\land P(\mathbb R,(0\in\mathbb R),(x\mapsto x)_t,1)=\mathrm{none}.
\end{aligned}
\]

1. **Objects:** Full real feasible domain, identity loss and a feasible zero initial.
2. **Quantifiers/order:** Six closed conjuncts.
3. **Assumptions:** None; topological/geometric properties are asserted, not premises implying attainment.
4. **Conclusion:** Nonempty closed convex domain with a concrete failed positive-prefix selection, contrasting successful initialization.
5. **Indices/boundaries:** Time 0 has empty loss sum; time 1 has objective x. No infinity-valued losses appear.
6. **Information:** Failure is mathematical nonattainment in a noncompact domain, not a computational timeout.
7. **Excluded scope:** Closedness and convexity are not an attainment guarantee. No all-positive-time failure claim is literally stated, even though the stream is defined for every t.

## Proposition 8

For r0(x)=x and later r_t(x)=x²−x, time-1 selection fails but time-2 selection returns zero. Zero minimizes the two-loss sum, which equals x² at every real x.
\[
\begin{aligned}
&P(\mathbb R,(0\in\mathbb R),r,1)=\mathrm{none}
\land P(\mathbb R,(0\in\mathbb R),r,2)=\mathrm{some}(0)\\
&\land\operatorname{IsMinOn}(x\mapsto\sum_{i<2}r_i(x),\mathbb R,0)
\land[\forall x\in\mathbb R,\ \sum_{i<2}r_i(x)=x^2].
\end{aligned}
\]

1. **Objects:** Same whole-line domain and zero initial, new nonconstant-in-time stream r.
2. **Quantifiers/order:** Four conjuncts; only the fourth explicitly quantifies x, while IsMinOn contains all feasible-point comparisons.
3. **Assumptions:** None; failure, recovery, minimum and function equality are asserted.
4. **Conclusion:** Actual Option transition from none at time 1 to some 0 at time 2, minimum specification and exact global quadratic sum identity.
5. **Indices/boundaries:** The second prefix contains only indices 0 and 1. Its cancellation is x+(x²−x)=x². The first prefix is x. No claim beyond time 2.
6. **Information:** P recomputes from the entire available strict prefix; it does not bind the prior Option output. Adding the next loss can restore attainment.
7. **Excluded scope:** No absorbing-failure semantics, reset procedure, or automatic general recovery is present. The minimum clause does not explicitly assert uniqueness; exact selected zero and quadratic identity are separate asserted facts, not supplied proofs.

## Completeness and findings

All eight propositions are reconstructed, with top-level conjunct counts 7,3,5,6,1,4,6,4 and seven semantic slots each. All four generic and seven concrete definitions have been expanded. No unresolved type or semantic-context ambiguity was identified.

Key distinctions are finite history versus finite feasible set, subtype initialization versus arbitrary tied selection, EqOn versus global equality, and direct-prefix recovery versus recursive Option failure propagation. None of the #check expressions proves these assertions or supplies a source-acceptance verdict. No compilation was run.
