# Three extended-real proximal types: neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium, with runtime model and effort not independently attested. This automated actor has reused related staged history; it is not fresh source-naive, absolutely blind, human, or externally independent. Only the current neutral input was read for this task. No production body, other module, source book, contract, compiler result, or source verdict was consulted.

The supplied context and three proposed headers are reconstructed below. Definitions are borrowed context, not new definitions owned by this packet. No proof or acceptance is claimed.

## Exact context

E has NormedAddCommGroup E and InnerProductSpace R E. The first theorem has no CompleteSpace requirement. The second and third additionally assume CompleteSpace E. None assumes FiniteDimensional.

Write extended reals as \(\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}\), with top \(+\infty\) and bottom \(-\infty\). The context specifies
\[
\operatorname{Proper}(f):
(\forall y\in E,\ f(y)\ne-\infty)
\ \land\
(\exists a\in E,\ \exists r\in\mathbb R,\ f(a)=\iota(r)).
\]
The finite witness is ambient; it need not belong to V. Here \(\iota\) denotes the embedding of a real into EReal.

The supplied subdifferential is the global supporting set
\[
\partial f(z)=
\{g\in E:\ \forall y\in E,\
f(z)+\iota(\langle g,y-z\rangle)\le f(y)\}.
\]
Although its nonemptiness is required only at z∈V, its support comparison ranges over every ambient y, including points outside V. No supporting-vector bound, single shared supporting vector, or selected policy is assumed.

Write \(F(z)=(f(z)).\mathrm{toReal}\). This is a total real conversion, not an order-preserving replacement of all extended-real arithmetic without finiteness. For EReal, both infinite endpoints convert to zero; finite embedded reals convert to their real values. Thus the finiteness hypotheses and the support/properness context cannot be discarded when interpreting F as the finite part.

For real-valued ψ, write
\[
D_\psi(a,b)=\psi(a)-\psi(b)-(\operatorname{fderiv}_{\mathbb R}\psi(b))(a-b).
\]
Its second argument is the derivative base. The total fderiv defaults to zero if ψ is not differentiable there. IsMinOn A V p means \(\forall z\in V,\ A(p)\le A(z)\); it does not supply p∈V. All statements are deterministic, with no randomness, information filtration or actual iteration.

## 1. finitePart_convex_of_subdifferentiable

In any real inner-product space with the stated normed structure, suppose V is convex, f is proper in the ambient sense above, and f has at least one global supporting vector at each point of V. Then the real finite-part function F is convex on V.

\[
\begin{aligned}
\forall f:E\to\overline{\mathbb R},\ \forall V\subseteq E,\quad&
\operatorname{Convex}(V)\ \land\operatorname{Proper}(f)\\
&\land\bigl[\forall z\in V,\ \exists g\in E,\
\forall y\in E,\ f(z)+\iota(\langle g,y-z\rangle)\le f(y)\bigr]\\
&\Longrightarrow \operatorname{ConvexOn}_{\mathbb R}(V,F).
\end{aligned}
\]

1. **Objects:** A real inner-product space E, extended-real function f, set V, and real function F=f.toReal.
2. **Quantifiers/order:** Universal E and its normed/inner-product structures, then f,V,hV,hp,hs. The support assumption has order for each z∈V, some g, then every ambient y. Different z may have different supporting vectors.
3. **Assumptions:** Convex V; no bottom anywhere; an ambient finite point; and nonempty global subdifferential at every feasible point. Completeness and finite dimension are absent. No separate ConvexOn EReal f hypothesis or explicit feasible finiteness premise is supplied.
4. **Conclusion:** ConvexOn R V F, which includes the set's convexity and the usual real-valued convex inequality on it. The conclusion is about F on V, not global convexity of f.
5. **Finite/infinite and degenerate boundaries:** Top values outside V are not prohibited by properness. Bottom is prohibited everywhere. The ambient finite witness together with a global support comparison at a feasible point excludes a top value at that point in the intended assumption semantics; bottom is already excluded. This is why global support differs from support restricted to V. V may be empty: then support requirements and function convexity comparisons are vacuous, although properness still requires an ambient finite witness. Singleton V and zero-dimensional E are allowed.
6. **Information/regularity:** Static supporting-vector existence, not a produced selection. No differentiability of f, norm bound on supports, closedness or boundedness of V, or nonempty interior is required.
7. **Excluded scope/proof boundary:** This header proposes the convexity implication; it supplies no proof of it or separate finiteness lemma. It does not assert f finite everywhere or convert top/bottom into legitimate finite loss values merely by invoking toReal. No source conditions are inferred from names.

## 2. proximal_finitePart_minimizer_iff

In the additionally complete space, let p be a supplied feasible point and assume f is finite at every feasible point. For arbitrary ψ, real η and ambient center x, minimizing the extended-real objective f plus the embedded real divergence regularizer at p is equivalent to minimizing the corresponding real finite-part objective there.

\[
\begin{aligned}
&\forall f:E\to\overline{\mathbb R},\ \forall V\subseteq E,\
\forall\psi:E\to\mathbb R,\ \forall\eta\in\mathbb R,\ \forall x,p\in E,\\
&p\in V,\qquad
\forall z\in V,\ f(z)\ne+\infty\ \land f(z)\ne-\infty\\
&\Longrightarrow
\operatorname{IsMinOn}\bigl(z\mapsto f(z)+
\iota(\eta^{-1}D_\psi(z,x)),V,p\bigr)\\
&\hspace{5em}\Longleftrightarrow
\operatorname{IsMinOn}\bigl(z\mapsto F(z)+\eta^{-1}D_\psi(z,x),V,p\bigr).
\end{aligned}
\]
More directly, with \(R(z)=\eta^{-1}D_\psi(z,x)\), this equivalence compares
\[
[\forall z\in V,\ f(p)+\iota(R(p))\le f(z)+\iota(R(z))]
\quad\Longleftrightarrow\quad
[\forall z\in V,\ F(p)+R(p)\le F(z)+R(z)].
\]

1. **Objects:** E with explicit CompleteSpace as well as the normed real inner-product structure; f:E→EReal, V:Set E, ψ:E→R, η:R, and x,p:E.
2. **Quantifiers/order:** f,V,ψ,η,x,p, then hp and hfin. The conclusion is an iff for the same p and same regularizer on both sides; no minimizer is chosen.
3. **Assumptions:** p∈V and both non-top and non-bottom conditions at every z∈V. No convexity of V, properness of f, support condition, differentiability of ψ, or positivity/nonzero condition on η is assumed here.
4. **Conclusion:** Exact equivalence of two global-over-V minimizer predicates. It does not assert either predicate holds. p's membership ensures the finite-value premise covers the objective at p as well as every comparison point.
5. **Signs/normalization/boundaries:** The real scalar η⁻¹ multiplies D before embedding into EReal. η may be positive, negative, or zero; Lean's real inverse at zero is zero, so the regularizer vanishes at η=0. Finiteness is local to V, so both infinities may occur outside V. Empty V is ruled out by hp; singleton V is allowed. The center x need not be feasible or have finite f(x).
6. **Information/derivative semantics:** No derivative premise on ψ even at x; D uses its total fderiv convention. No value of f(x) is used in the regularizer. This is a static order/comparison conversion in a complete inner-product context, not an iterative algorithm or existence result.
7. **Excluded scope/proof boundary:** Neither existence nor uniqueness follows as an asserted conclusion. IsMinOn does not replace hp. Completeness is an explicit binder even if a weaker ambient context might suffice mathematically. No proof of the equivalence or production identity is supplied.

## 3. proximal_one_step_extended

In the complete real inner-product context, suppose V is convex, f is proper, and every feasible point has a global supporting vector. Let η>0, and let p∈V be a supplied minimizer over V of f plus the embedded divergence regularizer centered at x. Require ψ to be ambient differentiable at both x and p. Then every feasible u satisfies the finite-part loss comparison with two subtracted divergence residuals.

\[
\begin{aligned}
&\forall f:E\to\overline{\mathbb R},\ V\subseteq E,\quad
\operatorname{Convex}(V),\ \operatorname{Proper}(f),\
[\forall z\in V,\ \partial f(z)\ne\varnothing],\\
&\forall\psi:E\to\mathbb R,\ \eta\in\mathbb R,\quad\eta>0,\qquad
\forall x,p\in E,\quad p\in V,\\
&\operatorname{DifferentiableAt}_{\mathbb R}(\psi,x),\quad
\operatorname{DifferentiableAt}_{\mathbb R}(\psi,p),\\
&[\forall z\in V,\
f(p)+\iota(\eta^{-1}D_\psi(p,x))
\le f(z)+\iota(\eta^{-1}D_\psi(z,x))]\\
&\Longrightarrow
\forall u\in V,\quad
\eta(F(p)-F(u))\le
D_\psi(u,x)-D_\psi(u,p)-D_\psi(p,x).
\end{aligned}
\]

1. **Objects:** A complete real inner-product space, extended-real f, convex feasible set V, real ψ, positive η, ambient center x, feasible supplied p, and feasible comparison point u.
2. **Quantifiers/order:** f,V,hV,hf,hs,ψ,η,hη,x,p,hp,hdx,hdp,hmin, followed by all u with membership. The nested support order remains every feasible z, some vector, every ambient y. The same p,x,η and ψ occur throughout.
3. **Assumptions:** Properness and global support only required in the stated scopes; positive η; membership p∈V; ψ differentiable at both x and p; actual extended-real IsMinOn input. No f differentiability, ψ convexity, finite dimension, closed V, x∈V, or derivative-at-u premise appears.
4. **Conclusion:** A real inequality involving η times F(p)−F(u). Endpoint order and signs are exactly +D(u,x)−D(u,p)−D(p,x). It is neither an inequality directly subtracting arbitrary infinities nor a bound with either negative residual omitted.
5. **Finite/infinite and boundary cases:** Feasible values are protected by the proper/global-support assumptions, rather than a separately written hfin. The ambient finite witness need not be in V; top outside V remains allowed and bottom anywhere remains excluded. x can be outside V and f(x) may be top without appearing in the comparison. η=0 and negative η are excluded here. u=p is allowed and gives cancellation; p=x is allowed when feasible. Zero-dimensional E and singleton V are permitted; hp rules out empty V.
6. **Information/regularity:** No temporal rule or recurrence. p is supplied with a global constrained minimum property, not constructed from x or from observations. Differentiability at the two actual ψ base points is explicit; no default-fderiv substitute can discharge those hypotheses. The current loss f has no derivative premise.
7. **Excluded scope/proof boundary:** No minimizer existence, uniqueness, policy, probability, or online guarantee is supplied. Without ψ convexity the residuals are not asserted nonnegative, so they cannot be dropped on that basis. The type proposes the comparison but does not prove it or any implication between the three headers.

## Completeness

All three proposed statements have complete generic contexts, quantifiers, assumptions and seven-slot reconstructions. No unresolved semantic-context issue was identified. The input supplies the borrowed definitions needed for the reading. No external source assumptions, proof, compiler result, publication status, or chapter/Goal acceptance is inferred.
