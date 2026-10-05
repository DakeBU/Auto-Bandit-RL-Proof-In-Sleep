# Restricted-input reconstruction: Q0–Q2 and M01–M03

This fresh pass read only `blind-packet-v1.md` in this directory as mathematical file input. No source, public-name map, proof body, prior verdict, or other file was consulted. Earlier unrelated actor history is not erased or claimed absent. The actor serves as a distinct automated decoder, requested GPT-6 Astra / medium; the runtime model is not attested. This is not human or external-model review. No compilation, proof validation, source acceptance, chapter completion, or Goal completion is certified.

Independent SHA-256 of the packet's exact raw bytes:
`0c48ea772dfffc7df98f06c3f59a4a49206642fb2e7a991e2b3fcfac51c78974`.

## Shared interpretation

E is a complete real inner-product space with its normed additive commutative group structure. The packet does not assume finite dimensionality. Write ι(r) for embedding r∈ℝ into EReal, top for +∞, bottom for −∞, and F(z)=toReal(f(z)) for the specifically supplied real-valued conversion of an extended-real f. The derivative in M03 is the ambient real derivative of this exact globally defined F at x; no arbitrary extension or existentially chosen finite-valued representative is used.

Imported EReal order/arithmetic, toReal, gradient and neighborhood notation are interpreted mathematically here, not verified against their implementation. In particular a converted real value alone does not establish that the original EReal value was finite. M01 states the local equality that gives that interpretation near the specified point. Interior means ambient topological interior, not relative interior in an affine hull.

## Q0 — below-top domain

1. **Objects:** f:E→EReal and a subset D_f=Q0(f) of the complete real inner-product space E.
2. **Quantifiers:** Defined for every f, with membership tested at every point z∈E.
3. **Assumptions:** No convexity, non-bottom, properness, or differentiability condition.
4. **Conclusion:** \(D_f=\{z\in E:f(z)<+\infty\}\).
5. **Normalization:** Strict inequality against top. It is not defined using toReal or finite-real witness existence.
6. **Information/probability:** Deterministic set definition; no probability or temporal information condition.
7. **Boundary:** Under the usual EReal order interpretation, −∞ is included and +∞ excluded. D_f can be empty or have empty ambient interior. Without a no-bottom hypothesis, it is not the same as the finite-real-valued locus.

## Q1 — real-height epigraph

1. **Objects:** f and epi_R(f)=Q1(f)⊆E×ℝ.
2. **Quantifiers:** Every f and every pair (z,r) with finite real coordinate r.
3. **Assumptions:** None on values or regularity.
4. **Conclusion:** \(\operatorname{epi}_{\mathbb R}(f)=\{(z,r):f(z)\le\iota(r)\}\).
5. **Normalization:** Non-strict inequality, real rather than extended-real height.
6. **Information/probability:** Deterministic membership condition.
7. **Boundary:** At a top-valued point the height fiber is empty; at a bottom-valued point it is all ℝ; for finite f(z)=ι(a) it is [a,∞), under ordinary EReal order interpretation. An entirely empty epigraph is permitted.

## Q2 — epigraph convexity

1. **Objects:** Extended-real f and its real-height epigraph in the product real space E×ℝ.
2. **Quantifiers:** Every f:E→EReal.
3. **Assumptions:** No properness, no-bottom condition or finite witness is built into the definition.
4. **Conclusion:** Q2(f) means epi_R(f) is convex over ℝ.
5. **Normalization:** Ordinary nonnegative convex-combination weights summing to one; no loss rescaling.
6. **Information/probability:** Deterministic geometric predicate.
7. **Boundary:** Empty epigraphs count as convex. Neither global finiteness nor nonempty domain/interior follows from the predicate alone. Additional hypotheses in M03 must not be inferred from Q2 itself.

## M01 — local equality to the canonical real conversion

1. **Objects:** f:E→EReal, its canonical real conversion F(z)=toReal(f(z)), domain D_f, and point x.
2. **Quantifiers:** Every f with the global no-bottom property, then every x∈interior(D_f). The conclusion is an eventual statement over z in the neighborhood filter of x.
3. **Assumptions:** \(\forall z\in E,\ f(z)\ne-\infty\), and x lies in the ambient interior of D_f. No epigraph convexity or differentiability is assumed.
4. **Conclusion:**
   \[
   \forall^{\text{eventually}}z\text{ near }x,\quad\iota(F(z))=f(z).
   \]
   Equivalently in this topological setting, the equality holds on some neighborhood of x. This identifies the values there as finite real values, including the value at x.
5. **Normalization:** Exact equality from embedding to original value, with coefficient one. The neighborhood size is existential, not prescribed uniformly or quantitatively.
6. **Information/probability:** “Eventually” here is topological neighborhood language, not a time limit, probability-one event, or stochastic convergence statement.
7. **Boundary:** The equality is local near x, not for all E. +∞ values may occur away from that neighborhood. Merely x∈D_f, or relative-interior membership, does not match the premise. A function with empty ambient interior offers no x satisfying it. No derivative or convexity conclusion is made.

## M02 — real convex first-order support inequality

1. **Objects:** V⊆E, an everywhere real-valued f:E→ℝ, points x,y∈V, and the ambient gradient ∇f(x).
2. **Quantifiers:** Every V,f with ConvexOn ℝ V f, then every x,y∈V at which the specified differentiability assumption holds at x.
3. **Assumptions:** ConvexOn ℝ V f (including convexity of V and the convex-function inequality on it); x∈V; y∈V; DifferentiableAt ℝ f x. Differentiability is ambient at x, not merely within V. There is no differentiability assumption at y or all other feasible points.
4. **Conclusion:**
   \[
   f(x)+\langle\nabla f(x),y-x\rangle\le f(y).
   \]
   The affine first-order approximation at x is a lower bound at every allowed y.
5. **Normalization:** Inner product has argument order gradient then y−x; coefficient one, no residual, norm-square term, or smoothness constant.
6. **Information/probability:** Deterministic support comparison. There is no feedback oracle, history, algorithm, or random gradient.
7. **Boundary:** No openness, closedness, nonempty-interior, boundedness, or finite-dimensional condition on V. If V is empty there are no x,y meeting the premises. Boundary points of V are allowed if ambient differentiability holds. The conclusion is restricted to y∈V; global convexity on E is not required.

## M03 — extended-real global support from an interior derivative

1. **Objects:** f:E→EReal, D_f, epigraph convexity Q2(f), the canonical real function F(z)=toReal(f(z)), gradient g=∇F(x), interior point x, and arbitrary query y∈E.
2. **Quantifiers:** For every f with the global no-bottom and epigraph-convexity hypotheses, choose any x∈interior(D_f) at which F is ambient differentiable. For every y∈E, the displayed inequality holds. The gradient is fixed at x before the arbitrary query y and does not depend on that query.
3. **Assumptions:**
   \[
   \forall z,\ f(z)\ne-\infty,\quad Q2(f),\quad
   x\in\operatorname{interior}(D_f),\quad
   \operatorname{DifferentiableAt}_{\mathbb R}F(x).
   \]
   There is no membership, differentiability, or finite-value assumption on y. No differentiability on a whole neighborhood is required, only differentiability of the canonical F at x.
4. **Conclusion:**
   \[
   f(x)+\iota\!\left(\left\langle\nabla F(x),y-x\right\rangle\right)\le f(y)
   \qquad\text{for every }y\in E.
   \]
   This is an EReal inequality providing an all-query affine support at x, not a real inequality restricted to the effective domain.
5. **Normalization:** Gradient of precisely z↦toReal(f(z)), at x; its inner product is first a real scalar and then embedded into EReal. The inequality retains f(x), not an unqualified global replacement of f by its real conversion. Coefficient is exactly one, no additive error.
6. **Information/probability:** Deterministic mathematical support statement. M01 identifies F with f locally after embedding near x under the same interior/no-bottom assumptions; that local fact must not be promoted to a global finite-part identity. There is no probabilistic or temporal information structure.
7. **Boundary:** At x the assumptions provide finite f(x). At y∈D_f, global no-bottom makes f(y) finite; at y∉D_f, the usual EReal order interpretation gives f(y)=+∞ and the all-y inequality still includes that case. No bottom value occurs anywhere under the stated global premise. An empty or empty-interior domain gives no admissible x. Mere domain membership or relative interior does not replace ambient interior. The result does not assume F is globally convex on E or globally differentiable; outside the finite domain its imported conversion behavior does not itself encode f's infinite values.

## Limits

All three definitions and three unproved headers receive seven-slot coverage. The key distinction is between M01's neighborhood equality, M02's real support bound for y∈V under its full convexity/membership/differentiability premises, and M03's EReal support inequality for every ambient query y using the canonical finite-part derivative at an interior point. No proof or imported implementation was inspected, and no source or acceptance claim follows.
