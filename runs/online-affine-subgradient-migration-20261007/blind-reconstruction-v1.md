# Blind reconstruction v1

Actor task: `/root/affine_blind`.
Verdict: `blind-reconstructed`.
Evidence boundary: read only `blind-packet-v1.md`. This is a neutral statement reconstruction, not source acceptance, chapter acceptance, or Goal completion. Requested settings: GPT-6 Astra / medium. These are requested settings only; this report makes no runtime, human, or external attestation.

## Borrowed contexts: two; owned definitions: zero

**S (borrowed).** For a real inner product space V, an extended-real-valued function h, and a point z, S(h,z) consists of all vectors giving a global affine lower support at z. The test ranges over every ambient point, including when h takes infinite values. No finite-value premise is built into S.

\[
S(h,z)=\{q\in V:\ \forall w\in V,\ h(z)+\iota(\langle q,w-z\rangle)\le h(w)\},
\]
where \(\iota:\mathbb R\to\overline{\mathbb R}\) is the canonical embedding and arithmetic/order are those of EReal. The displayed compiled binders of S require a normed additive commutative group and real inner product structure, but not finite dimensionality.

**P (borrowed).** For a type V and a function h into EReal, P says that h never equals bottom and that at least one point has a real, finite value. The compiled binders of P do not require a vector space or inner product structure.

\[
P(h)\iff (\forall z\in V,\ h(z)\ne-\infty)\ \land\
(\exists z\in V\ \exists r\in\mathbb R,\ h(z)=\iota(r)).
\]

These are two contextual definitions supplied to interpret L, not definitions owned by this reconstruction.

## One theorem L: seven slots

### 1. Spaces and objects

**Natural language.** E and F are arbitrary finite-dimensional real inner product spaces with their normed additive commutative group structures. The function f maps F into EReal, A is a continuous real-linear map from E to F, b is a vector of F, and x is a vector of E. The adjoint is the Hilbert adjoint from F to E; completeness needed for it is supplied by the finite-dimensional real inner product structures.

**LaTeX.**
\[
E,F\text{ finite-dimensional real inner product spaces},\quad
f:F\to\overline{\mathbb R},\quad A\in\mathcal L_{\mathbb R}(E,F),\quad
b\in F,\quad x\in E,\quad A^*:F\to E.
\]

### 2. Quantifier order

**Natural language.** Universally quantify E and F and their displayed structures, then f. Assuming P(f), universally quantify A, b, and x. For every element of the full adjoint image of S(f,Ax+b), membership in the composite support set follows. Equivalently, every g in F satisfying the support inequality at Ax+b yields A* g satisfying the composite support inequality for every y in E. The finite witness in P is existential inside the assumption; it is not required to equal Ax+b.

**LaTeX.**
\[
\forall E,F\ \forall f:F\to\overline{\mathbb R},\quad
P(f)\Longrightarrow
\forall A\in\mathcal L_{\mathbb R}(E,F)\ \forall b\in F\ \forall x\in E,
\quad A^*[S(f,Ax+b)]\subseteq S(f\circ T,x),\qquad T(y)=Ay+b.
\]
Here E and F carry all structures in slot 1. Equivalently, after the same outer binders,
\[
\forall g\in F,\quad
\bigl[\forall z\in F,\ f(Ax+b)+\iota(\langle g,z-(Ax+b)\rangle_F)\le f(z)\bigr]
\Longrightarrow
\forall y\in E,\quad f(Ax+b)+\iota(\langle A^*g,y-x\rangle_E)\le f(Ay+b).
\]

### 3. Assumptions

**Natural language.** In addition to the space and map types, the sole explicit function hypothesis is P(f): f never takes negative infinity and has one finite real value somewhere in F. There is no assumption that f is convex, continuous, or closed, that A has a particular rank, or that f is finite at Ax+b.

**LaTeX.**
\[
(\forall z\in F,\ f(z)\ne-\infty)\ \land\
(\exists z_0\in F\ \exists r_0\in\mathbb R,\ f(z_0)=\iota(r_0)).
\]

### 4. Conclusion

**Natural language.** Pulling every global support vector of f at the affine image of x back through the adjoint gives a global support vector at x for the function y mapped to f(Ay+b). This is a one-way set inclusion of the full image, with no assertion of the reverse inclusion.

**LaTeX.**
\[
\boxed{\{A^*g:g\in S(f,Ax+b)\}\subseteq
S\bigl(y\mapsto f(Ay+b),x\bigr).}
\]

### 5. Constants

**Natural language.** There are no numerical bound constants, rates, tolerances, or hidden multiplicative factors. The inner product contribution has coefficient one. The translation b is arbitrary data, and the real value r in P is only an existential witness.

**LaTeX.**
\[
f(Ax+b)+1\cdot\iota(\langle A^*g,y-x\rangle_E)\le f(Ay+b).
\]

### 6. Information and probability

**Natural language.** This is a deterministic, universally quantified mathematical implication. It specifies no random variables, probability space, event, sampling procedure, algorithm, filtration, or measurable selection. S uses all ambient comparison points; it is not a finite-query test.

**LaTeX.**
\[
\forall z\in F\text{ in the antecedent support test};\qquad
\forall y\in E\text{ in the consequent support test}.
\]
There is no probability qualifier such as an almost-sure or high-probability event.

### 7. Boundaries and conventions

**Natural language.** L does not assert equality of the support sets, existence of a support vector, properness of the composite, a finite value at the query point, a converse chain rule, an algorithmic guarantee, a regret bound, or a coordinate conversion certificate. The finite witness for f can lie outside the affine range, so a finite witness for the composite is not supplied. If the support set on the left is empty, the inclusion is vacuous. EReal arithmetic is retained at infinite values; the reconstruction does not replace S with a convention that restricts its base point to the finite domain. In generic borrowed contexts P need not hold, and S still means exactly its displayed inequality; this theorem only claims its implication under P(f). No stronger infinite-dimensional generalization or weakening of assumptions is claimed.

**LaTeX.**
\[
A^*[S(f,Ax+b)]\subseteq S(f\circ T,x)
\quad\text{only};\qquad
P(f)\text{ is assumed},\quad P(f\circ T)\text{ is not asserted}.
\]
\[
S(f,Ax+b)=\varnothing\ \Longrightarrow\ A^*[S(f,Ax+b)]=\varnothing.
\]
No source identity, source-faithfulness verdict, proof-body property, or acceptance status is inferred.
