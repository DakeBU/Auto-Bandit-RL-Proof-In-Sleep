# Source-blind reconstruction of the three anonymous claims

I read only `blind-packet.txt` in this run directory. I did not inspect a source text, proof bodies, other repository files, identities, or prior verdicts. This is an independent model-based decoding of the supplied declarations, not an external human review and not a proof or compilation certificate. The supplied packet explicitly identifies its theorem headers as unproved data and is not compiled.

Raw-byte SHA-256, independently computed with Get-FileHash:

`0136781723e141c14e87ef5b545c9b0eccea3e8051f636693e49088101e83aca`

## Shared objects and complete definitions

The ambient space E is a real inner-product space with its normed additive commutative group structure. Each of the three theorem headers additionally binds a finite-dimensional structure over the reals. Thus each claim is universally parametrized by such a finite-dimensional E; none is stated here for arbitrary infinite-dimensional spaces. No particular coordinate dimension or positive dimension is assumed.

For V ⊆ E and x ∈ E, the defined normal cone is

\[
N_V(x)=\{g\in E : x\in V\ \land\ \forall y\in V,\ \langle g,y-x\rangle\le 0\}.
\]

Membership explicitly requires x ∈ V. Consequently N_V(x) is empty whenever x ∉ V, even if the displayed inequalities alone would hold. There is no normalization or nonzero requirement on g.

For f : E → EReal, where EReal is the extended real line, the effective domain supplied in the packet is

\[
\operatorname{dom}_{\mathrm{eff}}f=\{x\in E:f(x)<+\infty\}.
\]

This definition excludes +∞ but does not exclude −∞. It is reproduced as context and is not used explicitly in any of the three theorem headers or as a membership restriction in the next definition.

The extended indicator is

\[
I_V(x)=\begin{cases}0,&x\in V,\\+\infty,&x\notin V.\end{cases}
\]

Its effective domain is therefore V. The subdifferential is defined through the all-query support relation

\[
\partial f(x)=\left\{g\in E:\ \forall y\in E,\quad
 f(x)+\iota(\langle g,y-x\rangle)\le f(y)\right\},
\]

where ι embeds a real number into EReal. The quantifier ranges over every y ∈ E, including points outside the effective domain; it is not restricted to V or to finite-valued queries. The arithmetic and order are those of EReal. There is no separately imposed assumption that f(x) is finite, and this general definition does not prohibit f from taking −∞. For the indicator, values are only 0 and +∞, so mixed-infinity arithmetic is not needed to read the claims. A candidate g is fixed before the universal query y.

## Claim 1

1. **Objects and spaces.** An arbitrary finite-dimensional real inner-product space E, a subset V ⊆ E, a point x ∈ E, and the two sets ∂I_V(x) and N_V(x), both subsets of E.
2. **Quantifiers and order.** For every such E, every nonempty convex V, and every x ∈ E, equality holds. Equivalently, for every candidate g ∈ E, g satisfies the all-query support inequality for I_V at x if and only if x ∈ V and its inner-product inequality holds for every y ∈ V. The point x need not be chosen inside V.
3. **Assumptions.** Finite dimensionality, V.Nonempty, and convexity of V over ℝ. No closedness, boundedness, interior-point assumption, or positive-dimensionality is supplied.
4. **Exact conclusion.**
   \[
   \partial I_V(x)=N_V(x).
   \]
   This is equality of the complete sets, not an inclusion. Explicitly, the left membership condition is ∀y ∈ E, I_V(x) + ι(⟨g,y−x⟩) ≤ I_V(y); the right condition is x ∈ V together with ∀y ∈ V, ⟨g,y−x⟩ ≤ 0. If x ∉ V, both sets are empty: the cone requires x ∈ V, while any y ∈ V supplied by nonemptiness makes the indicator support inequality compare +∞ against 0.
5. **Constants.** Indicator values 0 and +∞, and the upper bound 0 in the normal-cone inequality. No rates, unspecified constants, or scale factors occur.
6. **Probability and information.** Entirely deterministic; there is no probability, randomness, filtration, algorithm, sampling, or temporal information condition. The support relation tests all queries y.
7. **Boundary and excluded regimes.** Points outside V are covered and give the empty sets. Boundary points inside V are covered. Nonclosed convex sets are permitted. Empty V, nonconvex V, and infinite-dimensional E are outside the declared assumptions; the header supplies no assertion for those regimes. The general effective-domain definition does not add a hidden restriction on x.

## Claim 2

1. **Objects and spaces.** An arbitrary finite-dimensional real inner-product space E, a nonempty convex subset V, and a point x in its topological interior.
2. **Quantifiers and order.** For every such E and V, every x ∈ E satisfying x ∈ interior V has the stated cone equality. The interior condition is an assumption attached to x, not an existential claim that V has an interior point.
3. **Assumptions.** Finite dimensionality, nonemptiness and real convexity of V, and x ∈ interior V. Here interior is the ordinary ambient topological interior in E, not relative interior in an affine hull. No closedness or boundedness is required.
4. **Exact conclusion.**
   \[
   N_V(x)=\{0_E\}.
   \]
   The cone contains exactly the zero vector; it is not the empty set. Equivalently, for every g ∈ E, x ∈ V and ∀y ∈ V, ⟨g,y−x⟩ ≤ 0 hold together if and only if g = 0.
5. **Constants.** The singleton consists of the ambient vector-space zero; the defining support bound is the real scalar zero. No other numeric constants occur.
6. **Probability and information.** Entirely deterministic, with the normal inequality universally quantified over points of V. No probability or information restriction appears.
7. **Boundary and excluded regimes.** No conclusion is supplied for a point merely in V, on a noninterior boundary, in relative interior only, or outside V. If V has empty ambient interior, no x meets the premise. There is no positive-dimensionality assumption, and the ordinary zero-dimensional interpretation remains included. The explicit finite-dimensional and nonempty/convex binders must be retained even if some could be weakened in a different theorem.

## Claim 3

1. **Objects and spaces.** An arbitrary finite-dimensional real inner-product space E, a vector x ∈ E of norm one, and the set B = {y ∈ E : ‖y‖ ≤ 1}.
2. **Quantifiers and order.** For every such E and every x with ‖x‖ = 1, the cone equals the stated ray. Membership on the right means: for a given g ∈ E, there exists a real scalar α, possibly depending on g and x, with α ≥ 0 and g = αx. It is not a single common α chosen for all g.
3. **Assumptions.** Finite dimensionality and ‖x‖ = 1, in addition to the ambient real inner-product structure. Nonemptiness and convexity of B are not separate premises in this header; B is explicitly defined. No assumption α > 0 or g ≠ 0 is present.
4. **Exact conclusion.**
   \[
   N_{\{y:\|y\|\le1\}}(x)
   =\{g\in E:\exists\alpha\in\mathbb R,\ \alpha\ge0\ \land\ g=\alpha x\}.
   \]
   Thus the normal cone to the closed unit ball at a unit-norm point is precisely the outward nonnegative ray through x. In full, the left membership condition is ‖x‖ ≤ 1 and ∀y ∈ E with ‖y‖ ≤ 1, ⟨g,y−x⟩ ≤ 0. Equality asserts both directions of this characterization.
5. **Constants.** Radius 1, center 0 as determined by the norm expression, boundary norm exactly 1, and scalar cutoff 0. The ray includes α = 0, hence includes g = 0; it is not just a strictly positive ray or a unit normal.
6. **Probability and information.** Deterministic. The cone inequality ranges over all points in the closed ball. There is no stochastic, temporal, or computational-information premise.
7. **Boundary and excluded regimes.** The set uses ≤ and is therefore the closed unit ball, not the open unit ball and not the unit sphere. The evaluation point lies on its boundary through ‖x‖ = 1. Interior points with norm < 1 and outside points with norm > 1 are not covered by this header. General radii and translated balls are not asserted. The cone definition independently makes it empty outside its set. A zero-dimensional E has no norm-one x, so the conditional statement has no such instance there. Infinite-dimensional spaces are outside the declared binders.

## Context limitations and ambiguity

The supplied mathematical declarations suffice to reconstruct the three statements and their quantifier scopes. They do not provide theorem bodies, proof validity, compilation results, original source wording, correspondence to any publication, or evidence of source fidelity. The import line cannot be independently checked under this read-only packet restriction; I have used only the definitions reproduced in the packet. No additional hidden source assumptions have been inferred. The precise implementation of general EReal operations is not reproduced, but the indicator claims only involve real finite inner products added to 0 or +∞, so the unusual −∞ regimes of an arbitrary f do not enter the three claims.
