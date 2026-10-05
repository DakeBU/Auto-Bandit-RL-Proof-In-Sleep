# Restricted-input reconstruction of M01–M04

This fresh pass used only `blind-packet-v1.md` in this run directory as mathematical file input. No source identity, public-name map, proof, prior verdict, or other file was read. Prior unrelated actor history is not erased or claimed absent. This is a distinct automated decoder role, requested GPT-6 Astra / medium, without runtime-model attestation or human/external-model review. No compilation, proof validation, source acceptance, chapter certification, or Goal certification is claimed.

Independent exact raw-byte packet SHA-256:
`4e1e1518278ede435073f62a8a238a3174119f653870b9ef07b02ef9532eb326`.

## Shared context and interpretation

E is a complete real inner-product space with its normed additive commutative group structure. No finite-dimensional assumption appears. All gradients and derivatives are over ℝ. For an extended-real f:E→EReal, write F(z)=toReal(f(z)) for the exact canonical real-valued function used in the packet. This is a globally defined conversion, not an arbitrary real extension or an existentially selected representative. Where f is finite, the usual EReal interpretation gives f(z)=ι(F(z)), with ι the real embedding. Imported toReal, gradient and IsMinOn semantics are interpretations here, not inspected implementations.

IsMinOn(f,V,x) is read as the comparison ∀y∈V, f(x)≤f(y). Membership x∈V is a separate premise in each header; it must not be smuggled into the comparison predicate or discarded because the name suggests membership. No theorem here asserts existence or uniqueness of a minimizer. The interior in M04 is ambient topological interior, not relative interior.

## M01 — real constrained first-order optimality

1. **Objects:** A subset V⊆E, everywhere real-valued f:E→ℝ, feasible candidate x, and ambient gradient ∇f(x).
2. **Quantifiers:** For every V,f,x satisfying the premises, an equivalence holds. Its right side quantifies over every y∈V, with the single gradient at x fixed independently of y.
3. **Assumptions:** ConvexOn ℝ V f; x∈V; DifferentiableAt ℝ f x. ConvexOn includes convexity of V and convexity of f restricted to it. Differentiability is ambient at the one candidate x, not merely differentiation within V. No differentiability at every other point, open neighborhood, or finiteness condition is needed for this real-valued helper.
4. **Conclusion:**
   \[
   \big(\forall y\in V,\ f(x)\le f(y)\big)
   \iff
   \big(\forall y\in V,\ 0\le\langle\nabla f(x),y-x\rangle\big).
   \]
   Thus global minimality on V is equivalent to nonnegative first-order change along every feasible displacement from x.
5. **Constants/normalization:** Inner product order is gradient then y−x; threshold is exactly zero and inequality is non-strict. No norm term, tolerance, or step size occurs.
6. **Information/probability:** Deterministic all-feasible-point criterion. It is not a condition tested only on sampled directions or an algorithmic convergence result.
7. **Boundary:** No openness, closedness, boundedness, or interior membership of V is required. Feasible boundary points are included; their gradients need not be zero. Empty V admits no x satisfying the membership premise. The criterion is about all feasible y, not all ambient y unless V=E.

## M02 — finite-value transfer of the minimizer comparison

1. **Objects:** Extended-real f:E→EReal, subset V, candidate x∈V, and canonical F(z)=toReal(f(z)).
2. **Quantifiers:** For every f,V,x, if every z∈V has finite f(z), compare the two minimizer predicates at that same candidate.
3. **Assumptions:** x∈V and ∀z∈V, f(z)≠+∞ and f(z)≠−∞. No convexity, nonempty-set premise beyond the given member, derivative, topology of V, or open-neighborhood witness is required by this helper.
4. **Conclusion:**
   \[
   \operatorname{IsMinOn}(f,V,x)
   \iff\operatorname{IsMinOn}(F,V,x).
   \]
   Explicitly, all comparisons f(x)≤f(y) for y∈V are equivalent to the corresponding real comparisons F(x)≤F(y).
5. **Constants/normalization:** Exact order transfer, no scaling or additive shift. Both infinities are explicitly excluded on V; below-top alone would not be this premise.
6. **Information/probability:** Deterministic conversion statement. Candidate membership ensures the finite-value assumption applies at x as well as each comparator y.
7. **Boundary:** f may take either infinity outside V. No neighborhood of V is asserted finite. Empty V gives no candidate meeting x∈V. The global conversion F must not be identified with f outside the specified finite set, and toReal alone does not certify finiteness.

## M03 — extended-real constrained optimality via a finite neighborhood

1. **Objects:** Extended-real f, feasible set V, open containing set U, feasible candidate x, canonical F=toReal∘f, and its ambient gradient at x.
2. **Quantifiers:** Every f,V,U,x with the stated conditions satisfies an equivalence; the support inequality then ranges over every y∈V. A single U is supplied for the entire V, not a separate local set for each comparison point.
3. **Assumptions:** V is convex and explicitly nonempty; x∈V; U is open; V⊆U; for all z∈U both infinite values of f(z) are excluded; ConvexOn ℝ V F; DifferentiableOn ℝ F U. The explicit convexity/nonemptiness/membership premises are retained even where some overlap logically with other premises. The open U makes differentiability on U applicable as ambient differentiability at x. Convexity is required on V, not on U.
4. **Conclusion:**
   \[
   \operatorname{IsMinOn}(f,V,x)
   \iff
   \forall y\in V,\quad 0\le\langle\nabla F(x),y-x\rangle.
   \]
   This is global minimality of the original extended-real f over V, characterized using the gradient of its precise canonical real conversion.
5. **Constants/normalization:** Exact zero threshold, unit coefficient, and displacement y−x. The gradient is taken at x only. No coercion is needed inside the real inner-product inequality; the minimizer comparison on the left uses EReal order.
6. **Information/probability:** Deterministic, all-feasible-point comparison. The finite-neighborhood hypothesis permits F to represent f after embedding throughout U, in particular near x and on V. This does not turn it into a global finite representation on E.
7. **Boundary:** x may be on the ambient boundary of V; no x∈interior(V) assumption appears here. U need not be convex or equal E. Either infinity may occur outside U. V need not be closed or bounded, and no gradient-zero conclusion follows from this header alone. Empty V is excluded explicitly. The query range is V, not all E.

## M04 — zero gradient at an ambient interior candidate

1. **Objects:** The same extended-real f, sets V,U, canonical F and candidate x, now with ambient interior membership in V.
2. **Quantifiers:** Every f,V,U,x satisfying all listed assumptions has the stated equivalence at that fixed candidate. No existence claim chooses an interior minimizer.
3. **Assumptions:** V convex and explicitly nonempty; x∈V; additionally x∈interior(V); U open with V⊆U; f finite at every z∈U (neither top nor bottom); ConvexOn ℝ V F; DifferentiableOn ℝ F U. Both candidate membership and the extra interior premise are retained exactly.
4. **Conclusion:**
   \[
   \operatorname{IsMinOn}(f,V,x)\iff\nabla F(x)=0_E.
   \]
   The constrained global minimizer comparison is equivalent to vanishing of the ambient gradient because the candidate is an ambient interior point under the supplied convexity and differentiability conditions.
5. **Constants/normalization:** Zero is the zero vector in E, not a scalar loss level. No assertion says the minimum loss is zero. The gradient is of exactly F=toReal∘f at x.
6. **Information/probability:** Deterministic equivalence, not a stopping rule, numerical tolerance, or stochastic stationarity guarantee. Finite representation is secured on U and locally around x; no global replacement of f by F is asserted.
7. **Boundary:** Boundary-only or merely relative-interior candidates do not meet the additional assumption. If V has empty ambient interior there is no applicable x, even when V has minimizers. Infinite values outside U remain allowed. Nonzero gradients at constrained boundary minima are not ruled out by this theorem. Infinite-dimensional complete E is permitted, and no strict convexity or uniqueness claim is made.

## Scope limits

The packet supplies four proof-omitted statements with enough scoped assumptions to distinguish the real helper, finite-set order transfer, all-feasible first-order criterion, and extra ambient-interior gradient-zero criterion. No derivative implementation, toReal code, proof body, or original source was read. The mathematical interpretations above do not constitute verification or acceptance of any declaration.
