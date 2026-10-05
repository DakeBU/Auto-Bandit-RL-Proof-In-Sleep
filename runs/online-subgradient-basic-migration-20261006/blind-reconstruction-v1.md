# Restricted current-packet reconstruction: S, N01, N02

Only `blind-packet-v1.md` in this directory was read as mathematical file input during this pass. No directory listing, source identity, other file, imported proof, earlier verdict, or compilation was used. Prior unrelated actor history is not erased; this is restricted current-packet reconstruction, not clean-history blinding. The actor is `/root/normal_blind`, requested GPT-6 Astra / medium, without runtime-model attestation or human/external-model review. No source matching, proof validation, compilation, chapter certification, or Goal certification is claimed.

Independent SHA-256 of exact raw packet bytes:
`ecbb1d5c872b805895ea89db4227831ad6e2d6baae660ecac3f017d03068970a`.

## Common context and reading boundary

E is a real inner-product space with NormedAddCommGroup and InnerProductSpace ℝ instances. Neither completeness nor finite dimensionality is required. These structures supply a zero vector, so E is nonempty, including in the possible zero-dimensional case. It would be incorrect to use an empty ambient type as a vacuous counterexample in this scoped setting.

The definition of S is fully displayed in the packet and was read. P, D and I are supplied imported context, not independently inspected bodies or proofs: P(f) excludes −∞ at every point and supplies at least one finite real witness; D_f={x:f(x)<+∞}; I_V is zero on V and +∞ outside. I does not occur in either target and is not used to replace their functions. Imported order/arithmetic and real convexity semantics are interpreted according to the supplied context and standard mathematical meaning, not implementation-verified.

Write ι(r) for the EReal embedding of r∈ℝ. Every inner product appearing in S is an ordinary finite real scalar before embedding. Thus the boundary readings below do not require evaluating a sum of opposite infinities: the added inner-product term is finite.

## S — globally supporting vectors

1. **Objects/spaces:** Extended-real f:E→EReal, base point x∈E, and a subset S_f(x)⊆E of candidate support vectors g in the real inner-product space.
2. **Quantifiers/information order:** The definition applies to every f,x. For a fixed candidate g, membership requires the inequality for every query y∈E. The vector is fixed before that universal query; no support vector is selected by the definition itself.
3. **Assumptions:** None on f's convexity, properness, domain, or regularity. No condition that f(x) be finite or that x belong to D_f is built into S.
4. **Conclusion/definition:**
   \[
   S_f(x)=\left\{g\in E:\forall y\in E,
       f(x)+\iota(\langle g,y-x\rangle)\le f(y)\right\}.
   \]
   It is the all-ambient-query affine support relation, not a relation limited to a feasible subset.
5. **Constants/normalization:** Exact coefficient one, displacement y−x, gradient/vector in the first inner-product slot, and non-strict inequality. No approximation error, norm bound, or normalization of g.
6. **Conclusion mode/information:** A deterministic set-valued definition, not a theorem producing a member or a probability event. No temporal or oracle-access restriction is present.
7. **Boundary:** Under ordinary EReal arithmetic with a finite addend, if f(x)=−∞ then every g∈E satisfies the condition, since −∞ plus a finite scalar is −∞ and is below every value. If f is identically +∞, every g is also admitted at every x, since top plus a finite scalar is top and top≤top. If f(x)=+∞ but f has even one non-top value elsewhere, no g can satisfy the global inequality. If f(x) is finite and some query has f(y)=−∞, the set is empty. Thus generic S does not itself enforce effective-domain membership or properness. The ambient zero vector ensures that statements S_f(x)=E indeed give a nonempty support set. These are mathematical readings of the displayed definition using interpreted EReal arithmetic, not imported proof verification.

## N01 — properness forces supported points into the domain

1. **Objects/spaces:** Extended-real f on E, supplied properness predicate P(f), point x, and an actual vector g∈S_f(x), with below-top domain D_f.
2. **Quantifiers/information order:** For every f satisfying P, for every x and g, if g satisfies the all-query support inequality at x then x∈D_f. The statement is universal in candidate vectors, not an existential guarantee that any support exists.
3. **Assumptions:** P(f), meaning both ∀y, f(y)≠−∞ and ∃y∃r∈ℝ, f(y)=ι(r); and g∈S_f(x). No convexity, continuity, differentiability, complete-space, or finite-dimensional assumption is supplied. Properness's finite witness need not equal x.
4. **Conclusion:** x∈D_f, exactly f(x)<+∞. Combined with the supplied global no-bottom condition, this means f(x) is finite in the usual EReal interpretation. The displayed conclusion itself is domain membership, not a derivative, convexity, or minimizer statement.
5. **Constants/normalization:** Strict below-top cutoff. No finite numeric upper bound is given, and no particular support vector or norm is prescribed.
6. **Conclusion mode/information:** Deterministic implication. By quantifier conversion, for each proper f it yields
   \[
   \{x:S_f(x)\ne\varnothing\}\subseteq D_f,
   \qquad x\notin D_f\Longrightarrow S_f(x)=\varnothing.
   \]
   These are logical readings of the header, not separately inspected theorems or a proof-validation claim. The all-y support premise makes the finite witness relevant to excluding support at a top-valued point.
7. **Boundary:** P excludes the generic identically-top case by its finite-witness conjunct and excludes all bottom-valued points by its universal conjunct. Without such restrictions S can be nonempty at points outside D_f, as the identically-top example shows. No converse inclusion or equality of domains is asserted: membership in D_f does not here produce a supporting vector. Empty effective domain cannot meet P, while points outside a proper function's domain may exist and then have empty S by the stated conversion.

## N02 — support existence implies convexity of a real function on V

1. **Objects/spaces:** An everywhere real-valued function f:E→ℝ, subset V⊆E, and the support relation for its pointwise EReal embedding \(\widetilde f(y)=\iota(f(y))\). The function's domain is all E, not a subtype V and not an extended-real function allowed infinite values.
2. **Quantifiers/information order:** For every f,V with V convex, assume for every x∈V that there exists some g_x∈E supporting the embedded function at x. Expanded order is
   \[
   \forall x\in V\ \exists g_x\in E\ \forall y\in E,
   \quad f(x)+\langle g_x,y-x\rangle\le f(y),
   \]
   using the finite-real interpretation of the embedded inequality. g_x may depend on x; there is no one common vector for all x. The query y is global, including y outside V.
3. **Assumptions:** Convex ℝ V and the nonempty-support condition at every x∈V. Support existence is an input hypothesis, not a conclusion obtained from assuming f is already convex. No continuity, differentiability, properness predicate, closure, boundedness, or nonempty-interior premise is listed. Real-valuedness supplies finite values everywhere.
4. **Conclusion:** ConvexOn ℝ V f. In ordinary real convex-combination form, this retains convexity of V and asserts
   \[
   f(\theta x+(1-\theta)y)\le\theta f(x)+(1-\theta)f(y)
   \quad(x,y\in V,\ 0\le\theta\le1).
   \]
   More generally its standard two-weight form has nonnegative real weights summing to one.
5. **Constants/normalization:** Weights sum to one; endpoints θ=0 and θ=1 are included, not replaced by strictly interior weights only. No additive error, smoothness constant, or strong-convexity term.
6. **Conclusion mode/information:** Deterministic implication from available global supporting vectors at feasible base points to convexity on V. It does not assert global convexity on all E, nor choose a measurable, continuous, or causal family x↦g_x. There is no probability or information restriction on support selection.
7. **Boundary:** Empty V is allowed: the support assumption is vacuous and ConvexOn on the empty set is the usual vacuous convexity property; E itself remains nonempty through its class structure. Singleton V is allowed, but the stated support premise at its point still concerns every ambient y. The global premise must not be rewritten as support only against y∈V, even if a weaker theorem might be possible. No support existence is guaranteed outside V, and no converse from convexity on V to global support is stated. Under the supplied P meaning the real embedding has a finite witness at the ambient zero vector, but P is not an extra assumption required by this header.

## Scope limits

All three items have seven-slot coverage. S is reconstructed from its full displayed definition; P/D/I remain supplied imported context, and no proof of them was read. The generic bottom and identically-top behaviors, the properness restriction behind N01, the inclusion/empty-outside logical readings, and the real-function/global-query/existence-as-premise structure of N02 are distinguished. No source, proof, or Goal certification follows from this reconstruction.
