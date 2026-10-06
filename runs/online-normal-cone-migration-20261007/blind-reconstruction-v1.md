# Restricted neutral semantic reconstruction

## Input and limits

I acted only as the semantic decoder. The sole file read for mathematical evidence was `blind-packet-v1.md` in this directory, including its neutral definitions, headers and printed types. I did not inspect source documents, proof bodies, repository files, provenance, sibling reports, earlier verdicts, or memory files. My conversation also contains system/developer instructions, an inherited workspace instruction message and the parent task assignment; therefore this is not a claim of a context-free actor or of erased history. Those materials were not used to identify a source or certify fidelity. The requested actor configuration was GPT-6 Astra / medium; this report makes no runtime model attestation. The packet labels its types compiled; I have not independently compiled anything. This is a reconstruction, not an acceptance verdict or external human review.

## Common notation and definitions

Universally take a type E with a normed additive commutative group and a real inner product space structure. The norm is the compatible norm of that structure. No coordinates, dimension positivity, or separate isometry certificate are supplied. Write ⟨g,y−x⟩ for `inner ℝ g (y - x)`.

### Owned definition N (separate reconstruction)

For every set V ⊆ E and point x ∈ E, N(V,x) is a set of vectors in E:

\[
N(V,x)=\{g\in E: x\in V\ \land\ \forall y\in E,\ y\in V\Rightarrow\langle g,y-x\rangle\le0\}.
\]

Thus membership quantifies universally over test points in V, and the query point must itself belong to V. The inner-product sign is nonpositive, with g in the first argument and y−x as displacement. The first conjunct is essential: for every x outside V, N(V,x) is empty, even when the inner-product condition would otherwise be vacuous. In particular N(∅,x)=∅. For x in V, the zero vector belongs. This definition imposes no nonemptiness, convexity, closedness, finite-dimensionality, or interior assumption. Its actual type has only the implicit E and the two structure instances, followed by V and x; it does not retain a finite-dimensional instance merely because the theorems do.

### Borrowed S and J (distinguished from N)

The packet gives a global predicate for every arbitrary function f:E→EReal and every x:

\[
S(f,x)=\{g\in E:\forall y\in E,\ f(x)+\iota(\langle g,y-x\rangle)\le f(y)\},
\qquad
J(V,x)=\begin{cases}0&x\in V,\\+\infty&x\notin V.\end{cases}
\]

Here ι is the real-to-EReal coercion. EReal also contains negative infinity; S is defined even for functions taking it. No properness, convexity, domain restriction, finiteness at x, or exclusion of negative infinity is part of S's definition. J uses only zero and top (+infinity). S's test point y ranges over all of E, not only V. These are supplied predicates, not an imported characterization silently added to N. Like N, these definitions have no finite-dimensional hypothesis.

## C01: seven semantic slots

1. **Ambient structure.** For every type E with the two structures above and a `FiniteDimensional ℝ E` instance. Finite dimensionality is a theorem binder, even though the definitions need less.
2. **Objects and query.** For every V:Set E and every x:E. The explicit query x has no membership or interior premise.
3. **Hypotheses.** V is nonempty and convex over ℝ; both remain explicit. No closedness is asserted.
4. **Quantifier scope.** E, its instances, V, a witness of V.Nonempty, a witness of Convex ℝ V, and then x are universally quantified in the displayed type. Equality entails equivalence for every g:E; S additionally tests every y:E, whereas N tests every y∈V.
5. **Predicates and normalization.** The function supplied to S is exactly the zero/top indicator J(V). The displacement is y−x, the real inner product is coerced to EReal on the S side, and the inequality is ≤. There is no scalar or norm normalization.
6. **Conclusion.** The sets are equal, in both directions:
   \[
   \forall x\in E,\quad S(J(V),x)=N(V,x).
   \]
   Expanded at every g, the assertion is
   \[
   [\forall y\in E,\ J(V,x)+\iota(\langle g,y-x\rangle)\le J(V,y)]
   \iff [x\in V\land\forall y\in E,\ y\in V\Rightarrow\langle g,y-x\rangle\le0].
   \]
7. **Boundaries.** This is an all-query feasible-set equality, including x outside V. For such a query the right side is empty; nonemptiness supplies a point of V where the left side's top-plus-finite ≤ zero condition cannot hold. Thin nonempty convex sets are allowed. Empty V is excluded: directly from the definitions, S(J(∅),x)=E while N(∅,x)=∅, so dropping nonemptiness changes the claim and fails. These observations unpack the supplied definitions; they are not additional source certification.

## C02: seven semantic slots

1. **Ambient structure.** Universally E with normed additive group, real inner product space, and finite-dimensional real vector-space instance.
2. **Objects and query.** Every V:Set E and every x:E to which an ambient-interior membership proof can be supplied.
3. **Hypotheses.** V.Nonempty, Convex ℝ V, and x∈interior V are retained. Neither closedness nor positive dimension is present.
4. **Quantifier scope.** Universally E and instances, V, nonemptiness and convexity witnesses, x, and its interior membership witness. The conclusion is an equality of sets of all g:E, not the selection of one vector.
5. **Predicate and normalization.** N is exactly the owned definition above. `interior` means interior in E's ambient norm topology, not relative interior in an affine hull. The zero on the right is the zero vector of E; there is no unit-norm assumption on x.
6. **Conclusion.**
   \[
   \forall x\in E,\quad x\in\operatorname{int}_E V\Rightarrow N(V,x)=\{0_E\}.
   \]
   Subject to the preceding nonempty and convex hypotheses, this says for every g:E that
   \[
   [x\in V\land\forall y\in E,\ y\in V\Rightarrow\langle g,y-x\rangle\le0]\iff g=0_E.
   \]
   It asserts both inclusion directions, including membership of zero.
7. **Boundaries.** Empty V is excluded and has no interior query. If V has empty ambient interior, the theorem has no admissible x; it does not say that every point of such V has normal set {0}. In particular a lower-dimensional convex set in a positive-dimensional ambient space must not be treated using relative interior here. In dimension zero, E has only its zero vector; every nonempty V is E and has ambient interior E, so the statement has an admissible query and its equality is meaningful. This case is not excluded by the binders.

## C03: seven semantic slots

1. **Ambient structure.** Universally E with normed additive group, real inner product space, and finite-dimensional real vector-space instance. No fixed dimension or coordinates are chosen.
2. **Objects and query.** Every x:E with norm exactly one. The feasible set is the closed unit norm ball B={y:E | ‖y‖≤1}, centered at zero with radius one.
3. **Hypotheses.** The sole additional explicit hypothesis is ‖x‖=1. There is no separately supplied nonemptiness, convexity or membership witness for B; norm equality itself entails x∈B. Neither arbitrary V nor an arbitrary radius is quantified.
4. **Quantifier scope.** Universally E, all three structure/class instances, x, and its norm-equality witness. Set equality quantifies over every g:E; on the right there exists α:ℝ for that g, with both 0≤α and g=α•x. On the left N universally tests every y:E with ‖y‖≤1.
5. **Sign and normalization.** Unit norm is exact, not ≤1 or merely nonzero. The normal inequality remains ⟨g,y−x⟩≤0, so the ray uses x with nonnegative real multipliers. α=0 is included. The operation • is real scalar multiplication.
6. **Conclusion.**
   \[
   \|x\|=1\Rightarrow
   N(\{y\in E:\|y\|\le1\},x)
   =\{g\in E:\exists\alpha\in\mathbb R,\ 0\le\alpha\land g=\alpha x\}.
   \]
   Equivalently, for every g:E,
   \[
   [\|x\|\le1\land\forall y\in E,\ \|y\|\le1\Rightarrow\langle g,y-x\rangle\le0]
   \iff\exists\alpha\in\mathbb R,\ 0\le\alpha\land g=\alpha x.
   \]
   Under the unit-norm hypothesis this describes the entire nonnegative ray, including zero; it is not just an inclusion or the existence of some outward vector.
7. **Boundaries.** No assertion is made here for interior or outside-ball queries, since their norm is not one. The ball itself is never empty, as it contains zero. Dimension zero is allowed in the ambient quantification, but then no x has norm one, so the conditional theorem has no admissible query. In positive dimensions the equality's zero multiplier is essential; replacing ≥0 with >0 omits an actual member. It does not assert a computable or measurable selection of α or g.

## Scope of reconstruction

All three targets are exact set equalities with their actual assumptions preserved. None supplies an algorithm, regret bound, probability model, source identity, provenance verdict, proof audit, or program-completion claim. Empty/thin/zero-dimensional observations above distinguish applicability from what the definitions themselves say; they do not weaken any retained binder.