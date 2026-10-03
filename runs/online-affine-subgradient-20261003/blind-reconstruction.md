# Source-blind semantic reconstruction

This AI decoding uses only the supplied neutral packet. It does not establish a proof, compare with a source, or constitute human or external review. Neither imported module was inspected.

## Seven semantic slots

1. **Ambient spaces and objects.** E and F are arbitrary finite-dimensional real inner-product spaces with normed additive group structures. They need not have equal dimensions. The function f maps F into the extended real numbers. A is an actual continuous real-linear map from E to F, b is a vector in F, and x is a vector in E. The operator A* denotes A.adjoint, the actual Hilbert adjoint from F to E, characterized here by <A* g,v>=<g,A v>.

2. **Complete quantification and properness.** For every such E and F, every f : F -> EReal satisfying the displayed predicate SourceProper, every A : E ->L[R] F, every b in F, and every x in E, the inclusion below holds. The properness hypothesis means exactly
   \[
   (\forall u\in F,\ f(u)\ne-\infty)
   \quad\text{and}\quad
   (\exists u_0\in F)(\exists r\in\mathbb R),\ f(u_0)=r.
   \]
   Thus f never takes negative infinity and takes at least one finite real value somewhere in F. Positive infinity is permitted elsewhere. The finite witness need not be in the affine image A(E)+b, and no condition states that f(Ax+b) is finite.

3. **Functions, points, and exact subdifferential convention.** Put T(y)=Ay+b and h=f composed with T, so h(y)=f(Ay+b). The source subdifferential is evaluated at Tx=Ax+b in F, while the target subdifferential is evaluated at x in E. The packet defines
   \[
   \partial q(w)=\{s:\ \forall v,\ q(w)+\langle s,v-w\rangle\le q(v)\},
   \]
   with the real inner product embedded in EReal and extended-real addition and order. Every test point ranges over its entire ambient space. There is no added rule in this definition declaring the subdifferential empty outside a finite domain.

4. **Image, adjoint, and output relation.** The claim is precisely
   \[
   A^*\bigl(\partial f(Ax+b)\bigr)
      \subseteq \partial(f\circ T)(x).
   \]
   Here the left side is an actual set image:
   \[
   \{p\in E:\ \exists g\in F,\ g\in\partial f(Ax+b)\ \land\ A^*g=p\}.
   \]
   It is not an inverse image, an image under an arbitrary named relation, or an existentially chosen surrogate operator. The conclusion is inclusion only. It does not assert equality, a reverse inclusion, uniqueness of a source subgradient, or that every target subgradient admits such a representation.

5. **Expanded global supporting inequalities.** Equivalently, for every g in F,
   \[
   \left[\forall u\in F,\ f(Ax+b)+\langle g,u-(Ax+b)\rangle\le f(u)\right]
   \Longrightarrow
   \left[\forall y\in E,\ f(Ax+b)+\langle A^*g,y-x\rangle\le f(Ay+b)\right].
   \]
   In set-inclusion form the same quantifiers read: for every p in E, if there exists g in F satisfying all the source supporting inequalities and p=A*g, then p satisfies all the target supporting inequalities. These are global inequalities, not directional, local, differentiability, or almost-everywhere assertions.

6. **Boundary and degenerate cases.** Neither zero-dimensional spaces nor the zero map A are excluded. If E is zero-dimensional, its only possible subgradient vector is zero, and the target function has a one-point domain. If F is zero-dimensional, properness forces f to be finite at its sole point, A and b are necessarily zero, and the composition is finite and constant. When A=0 in general, T(y)=b and A*=0. If f(b) is finite, the composition is a finite constant and its subdifferential on E is {0}; the source image is {0} when the source subdifferential is nonempty, and empty otherwise. If f(b)=+infinity, properness supplies a finite point elsewhere in F, so the source subdifferential at b is empty. The composition is then constantly +infinity and, under the packet's literal supporting-inequality definition, every vector in E is a target subgradient. More generally, whenever f(Ax+b)=+infinity, properness of f makes the source subdifferential empty, so the inclusion is vacuous. The composition need not be proper: the affine image may avoid every finite point of f. Since f never takes negative infinity, such a composition is identically +infinity, with target subdifferential all of E. If the composition has a finite value at some point but is +infinity at x, its target subdifferential at x is empty. At finite evaluation points source subdifferentials may still be empty; no nonemptiness is claimed. In every empty-source case the left image is empty.

7. **Assumptions absent and interpretation limits.** The header states no convexity, continuity or lower semicontinuity of f; no differentiability; no interior-point, relative-interior, or constraint qualification; no injectivity, surjectivity, full-rank or nonzero condition on A; and no nonemptiness assumption for either subdifferential. It does require finite-dimensionality of both spaces and continuity and linearity of A. It does not assert properness of the composition, a chain-rule equality, a reverse lifting of subgradients, an optimization guarantee, or validity in infinite-dimensional spaces. The report decodes the displayed unproved statement and definitions only; source fidelity and compiled correctness are outside this decoding task.
