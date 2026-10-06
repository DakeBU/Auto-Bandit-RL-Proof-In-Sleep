# Neutral reconstruction from restricted packet v1

Actor task: `/root/lipschitz_blind`. Requested configuration: GPT-6 Astra / medium. This records requested settings only; it does not attest the actual runtime model or effort. The only evidentiary input read was `blind-packet-v1.md`. No source identity, source PDF, repository content other than that packet, history, search, proof body, or prior verdict was consulted. Compiled binder information below is transcribed from the packet, not independently compiled or verified. This report makes no source-acceptance judgment.

## Owned definition B

Natural language: For an arbitrary normed additive commutative group E, an extended-real-valued function f, any subset V, and a nonnegative real L (possibly zero), B says that f takes genuinely finite real values at every point of V, and that the real representatives of those values satisfy the Lipschitz inequality with constant L on every pair of points of V.

LaTeX (write j for the real embedding into the extended reals):
\[
 B(f,V,L)\;:\!\iff\;
 \left(\forall x\in V\;\exists a\in\mathbb R,\ f(x)=j(a)\right)
 \land
 \left(\forall x\in V\;\forall y\in V,\
 |\operatorname{toReal}(f(x))-\operatorname{toReal}(f(y))|
 \le \ell\,\|x-y\|\right),\qquad \ell=(L:\mathbb R),\quad L\in\mathbb R_{\ge0}.
\]

Seven semantic slots:

1. **Objects.** E : Type u; an instance of NormedAddCommGroup E; f : E -> EReal; V : Set E; L : NNReal. The value of B is a proposition.
2. **Quantifier order.** The compiled parameter order is implicit E, a normed additive commutative group instance, then explicit f, V, L. Within the first conjunct: for every x, membership x in V implies existence of a real a with f(x) equal to its embedding. This witness may depend on x. Independently, the second conjunct universally quantifies x, its membership, y, its membership, then asserts the inequality. No single common value witness is required.
3. **Assumptions.** The only structure required by B's own compiled type is NormedAddCommGroup E. No inner product, real vector space, finite dimension, convexity, or properness is a parameter requirement. Finiteness on V is part of the defined proposition, not an omitted ambient assumption.
4. **Conclusion/content.** The two conjuncts jointly require real-valued finiteness on V and the displayed absolute-difference bound. Merely bounding toReal values without the first conjunct would not reconstruct B.
5. **Constants.** L is NNReal, so its real coercion ell is nonnegative and may equal zero. The same L bounds every pair. The multiplicative factor is exactly ell, with no additive term or hidden factor.
6. **Information/probability.** This is a deterministic property of a function and set. There is no distribution, event, confidence level, observation rule, filtration, or selection mechanism.
7. **Boundaries.** V is arbitrary and may be empty, in which case both conjuncts are vacuous. Values outside V are unconstrained. B is not intrinsically restricted to finite-dimensional or inner-product spaces. No positive L, nonempty V, or convex V is required.

## Owned theorem L

Natural language: In any finite-dimensional real inner-product space E with its specified compatible normed additive group structure, let f be extended-real valued, never minus infinity anywhere, and finite at at least one point. Suppose its real-height epigraph is convex. For each nonnegative real L, f is finite and L-Lipschitz on the ambient interior of its effective domain if and only if every vector supporting f globally at any point in that interior has norm at most L.

Here the effective domain is D(f) = {x : f(x) < +infinity}. Under the theorem's properness assumption, these are exactly the points where f is finite. A support vector at x must satisfy the inequality against every y in the whole ambient space, not just y in the interior.

LaTeX:
\[
\begin{gathered}
 E\text{ a finite-dimensional real inner-product space},\quad
 f:E\to\overline{\mathbb R},\\
 \left(\forall z\in E,\ f(z)\ne-\infty\right)
 \land\left(\exists z\in E\;\exists a\in\mathbb R,\ f(z)=j(a)\right),\\
 \operatorname{Convex}_{\mathbb R}\{(z,t)\in E\times\mathbb R:f(z)\le j(t)\},\quad
 L\in\mathbb R_{\ge0},\quad \ell=(L:\mathbb R),\\
 U=\operatorname{int}_{E}\{z\in E:f(z)<+\infty\}:\\[2pt]
 \left[
   \left(\forall x\in U\;\exists a\in\mathbb R,\ f(x)=j(a)\right)
   \land
   \left(\forall x\in U\;\forall y\in U,\
   |\operatorname{toReal}(f(x))-\operatorname{toReal}(f(y))|
       \le\ell\|x-y\|\right)
 \right]\\
 \quad\Longleftrightarrow\quad
 \forall x\in U\;\forall g\in E,\
 \left[\forall y\in E,\ f(x)+j(\langle g,y-x\rangle_{\mathbb R})\le f(y)\right]
 \Longrightarrow \|g\|\le\ell.
\end{gathered}
\]

Seven semantic slots:

1. **Objects.** E : Type u with NormedAddCommGroup E, InnerProductSpace Real E, and FiniteDimensional Real E; f : E -> EReal; proofs hp : P f and hc : C f; L : NNReal; U is the ambient interior of D f; x and g range over E. The norm is the one in the theorem's normed/inner-product structure.
2. **Quantifier order.** The actual compiled order is implicit E; NormedAddCommGroup instance; InnerProductSpace Real E instance; FiniteDimensional Real E instance; explicit f; hp : P f; hc : C f; then explicit L : NNReal; then the equivalence. Its right side is forall x : E, x in U -> forall g : E, g in S f x -> norm g <= real-coercion L. Membership in S contains a further universal quantifier over all y : E. The result bounds every admissible g, not an existentially chosen vector. The left-side quantifiers are those of B above with V = U.
3. **Assumptions.** P forbids bottom globally and supplies at least one finite real value, as two conjuncts. C is convexity of the real-height epigraph. Finite dimensionality is assumed for the theorem, unlike B. The packet supplies no closedness, lower semicontinuity, differentiability, boundedness, nonempty-interior, positive-dimension, positive-L, or support-existence hypothesis.
4. **Conclusion.** Exactly the displayed equivalence: finiteness and the L-Lipschitz inequality on U are equivalent to a uniform norm bound on all global support vectors based at points of U. Both implication directions are asserted. It does not independently assert support-vector existence.
5. **Constants.** L ranges over NNReal including zero, and the identical real coercion is used on both sides with coefficient one. There is no quantified negative real constant and no source-level claim for all real constants in this reconstruction.
6. **Information/probability.** The statement is deterministic. Support tests quantify over all ambient comparison points y. No oracle, feedback, probability, algorithm, regret bound, or certificate for selecting a vector appears.
7. **Boundaries.** Interior is ambient topological interior, not relative interior, closure, boundary, or the entire effective domain. U can be empty; then B and the universal support bound are both vacuous. At a point with no support vectors, the local universal support bound is vacuous; the theorem has no explicit existence conclusion. Properness guarantees a finite point somewhere but does not assert a nonempty ambient interior. No conclusion here extends the Lipschitz or support norm bounds to boundary points or points outside U.

## Borrowed context only: precise binder scopes

These five definitions are context and are not reconstructed as newly owned items:

- S: implicit E : Type u; NormedAddCommGroup E; InnerProductSpace Real E; explicit f : E -> EReal and x : E; result Set E. It consists of g satisfying f(x) + j(inner Real g (y - x)) <= f(y) for every ambient y.
- P: implicit E : Type u; explicit f : E -> EReal; result Prop. No algebraic, norm, or inner-product instance occurs in its compiled binders. Its content is global exclusion of bottom together with a finite-value witness.
- D: implicit E : Type u; explicit f : E -> EReal; result Set E. No structure instance is required. Its test is strict inequality below top, which by itself does not exclude bottom.
- Q: implicit E : Type u; explicit f : E -> EReal; result Set (E x Real). No structure instance is required. Its heights are real and are embedded into EReal for the inequality.
- C: implicit E : Type u; AddCommGroup E; Module Real E; explicit f : E -> EReal; result Prop. Its compiled binders do not require a norm or inner product. It asserts real convexity of Q f.

The ambient declarations in the displayed section are therefore not blanket assumptions on all six definitions. Only theorem L carries finite dimensionality in the supplied primary types. No independent proof checking or comparison with an identified external source was performed.