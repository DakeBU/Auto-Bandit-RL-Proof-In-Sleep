# Source-blind semantic reconstruction

This report reconstructs the neutral packet only. No source identity, theorem body, surrounding contract, imported proof, or prior verdict was inspected. It is an AI semantic decoding, not an independent human review or a correctness proof.

## Exact definition

For any function f : E -> EReal, any set V contained in E, and any nonnegative real constant L (including L=0), PairBound f V L means the conjunction

\[
\bigl(\forall x\in V,\ \exists a\in\mathbb R,\ f(x)=\operatorname{coe}(a)\bigr)
\quad\land\quad
\bigl(\forall x\in V,\ \forall y\in V,
 |\operatorname{toReal}(f(x))-\operatorname{toReal}(f(y))|
 \le L\|x-y\|\bigr).
\]

The finite-value witnesses are part of the definition, before the all-pairs condition involving toReal. The definition therefore requires actual finite function values on V; it is not merely a bound on the real projections of potentially infinite values. There is no requirement outside V. The witness a may depend on x, and every ordered pair of points of V is tested.

## Seven semantic slots for the full equivalence

1. **Ambient structure and objects.** E is any finite-dimensional real inner-product space with its normed additive group structure and the norm induced by the inner product. Its dimension may be zero. The function f takes values in EReal, the extended real line. The constant L belongs to NNReal, so its coercion to R is nonnegative and may be zero.

2. **Universal data and hypotheses.** For every such E, every f : E -> EReal, and every L in NNReal, the stated equivalence holds under the two hypotheses SourceProper f and IsConvexExtended f. Properness means exactly
   \[
   (\forall z\in E,\ f(z)\ne-\infty)
   \land (\exists z_0\in E)(\exists r\in\mathbb R),\ f(z_0)=\operatorname{coe}(r).
   \]
   The convexity hypothesis is convexity over real scalars of the real epigraph
   \[
   \{(z,r)\in E\times\mathbb R:\ f(z)\le\operatorname{coe}(r)\}.
   \]
   Positive infinity is permitted away from finite points. No other assumption on f, L, or the dimension is listed.

3. **Domain and location of every quantifier.** Define
   \[
   D=\{z\in E:f(z)<+\infty\},\qquad U=\operatorname{int}_E D.
   \]
   This is the interior in the ambient space E, not a relative interior in the affine hull of D. Properness excludes negative infinity, so every point of D, hence every point of U, has an actual finite real value. Both sides of the theorem concern every point of U. Neither side directly imposes the corresponding bound at points of D outside U or elsewhere in E.

4. **Actual ambient global supports.** At a point x, the packet defines
   \[
   \partial f(x)=\{g\in E:\ \forall z\in E,
     f(x)+\operatorname{coe}(\langle g,z-x\rangle)\le f(z)\}.
   \]
   The real inner product is embedded in EReal for addition and comparison. Every g satisfying this inequality at all ambient test points z is included. The test points are not restricted to U or D, and this is not a local supporting condition or a derivative notation. The theorem's norm bound quantifies over every member of this actual set.

5. **Full iff and expanded quantifier structure.** With U as above, the exact claim is
   \[
   \begin{aligned}
   &\left[
     (\forall x\in U,\exists a\in\mathbb R,\ f(x)=\operatorname{coe}(a))
     \land
     (\forall x\in U,\forall y\in U,
       |\operatorname{toReal}(f(x))-\operatorname{toReal}(f(y))|
       \le L\|x-y\|)
     \right]\\
   &\qquad\Longleftrightarrow
     \left[\forall x\in U,\forall g\in E,
       \bigl(\forall z\in E,
         f(x)+\operatorname{coe}(\langle g,z-x\rangle)\le f(z)\bigr)
       \Longrightarrow \|g\|\le L\right].
   \end{aligned}
   \]
   Thus finite values and the all-pairs L-Lipschitz inequality on U imply that all global supporting vectors at every x in U have norm at most L. Conversely, the stated uniform bound on all such supporting vectors implies both conjuncts of PairBound on U. This is a full equivalence, not only one direction and not a statement about some chosen support at each point. L is fixed before the point, pair, and support quantifiers; it is not chosen separately for each point or vector.

6. **Boundary, empty, and degenerate cases.** Empty interior is allowed even though properness makes D nonempty. When U is empty, the finite-value clause, the all-pairs clause, and the right-side norm clause are all vacuously true, so the equivalence still has its literal meaning. No nonempty-interior condition may be added. When L=0, the left side requires equal finite function values at every pair of interior points, and the right side requires every global supporting vector there to be zero; these assertions remain vacuous on empty U. In zero dimension E consists of its zero vector. Properness forces the sole function value to be finite, D and U are the whole singleton space, the only support vector is zero, and both sides hold for every allowed L. Positive-infinite values outside D do not occur in the all-pairs differences, but remain among the ambient comparison values in the supporting inequalities. Points on the boundary of D are not covered by the claimed norm or Lipschitz bounds merely because they are boundary points. At an individual point the universal support clause would be vacuous if its support set were empty; the packet states no additional support-existence premise and this report does not add one.

7. **Scope limits and missing information.** The packet does not assume differentiability, closedness of the epigraph, lower semicontinuity, a nonempty interior, a positive constant, a positive dimension, or an extra premise guaranteeing existence of subgradients. It does not assert the equivalence on the entire effective domain, its closure, or its relative interior; it supplies no boundary extension. It does not claim an infinite-dimensional version, an algorithm, a rate, or an application to a named loss. No source identity, original theorem label, proof method, implementation body, compilation evidence, or source-review result is supplied. Those facts cannot be recovered from the neutral packet and have not been guessed.

## Receipt interpretation

The accompanying receipt binds the raw bytes of the supplied packet and this report. Requested model and effort identify the assignment request only; this report does not independently attest the runtime model. No proof compilation or independent human review occurred in this decoding task.
