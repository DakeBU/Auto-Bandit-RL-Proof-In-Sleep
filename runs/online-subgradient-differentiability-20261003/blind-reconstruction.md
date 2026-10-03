# Source-blind reconstruction: differentiability and singleton support

Actor: `/root/closed_blind`, distinct decoder assigned GPT-6 Astra / medium.

Read inventory for this assignment: only `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-differentiability-20261003/blind-packet.txt`, read as text and hashed as raw file bytes. No source lookup, other repository read, or proof edit.

Packet SHA256: `07BEB3091AA31913521DD605F6AA519FBC8029077B5D2715B2BF3D940F455E64`.

Prior context disclosure: this actor has decoded earlier closed/proper, basic-subgradient, and interior-support packets in this conversation. Those assignments exposed related definitions and statement targets, but no external source text or source-review verdict was consulted. This is a source-blind reconstruction with prior mathematical-context exposure, not a decoder with a fresh conversation.

## Slot 1: Ambient objects and definitions

E is an arbitrary finite-dimensional real inner product space, with its normed additive commutative group structure. The function f is arbitrary from E to the extended reals. Its effective domain is {y : f(y) < positive infinity}, which by itself includes negative-infinity values. Its real epigraph consists of pairs (y,t) with finite real t and f(y) <= t. Extended convexity means convexity of this real epigraph in E times the reals.

The subdifferential at x is the set of g in E such that for every y in all of E,

    f(x) + <g,y-x> <= f(y).

The inner product is finite and embedded into EReal. This is a global support inequality, not one restricted to an effective domain, neighborhood, or auxiliary feasible set.

## Slot 2: Differentiability predicate

SourceDifferentiableAt f x means that there exists an everywhere-defined real-valued function h on E whose embedding into EReal agrees with f eventually in the neighborhood filter at x, and h is differentiable at x over the reals.

Thus f admits a real-valued representative on some ambient neighborhood of x, and this representative is differentiable at x. The witness h may be arbitrary away from that neighborhood; the predicate does not require f itself to be real-valued globally. Neighborhood equality is not equality only on a punctured neighborhood and not merely equality along the effective domain. It entails equality at x as well, and finite values of f throughout some neighborhood of x. DifferentiableAt has the standard Frechet-differentiability meaning for real normed spaces; its precise imported implementation was not inspected.

## Slot 3: Full equivalence and its quantifiers

For every such E and f with convex real epigraph, and every point x for which there exists a finite real r with f(x)=r,

    SourceDifferentiableAt f x
    if and only if
    there exists g in E such that SourceSubdifferential f x is exactly {g}.

The right side asserts existence and uniqueness of a global supporting vector. It is stronger than saying that there is at most one subgradient and stronger than asserting that a selected g belongs to the subdifferential. Expanded, there is g that satisfies the support inequality for every y, and every vector satisfying that inequality for every y equals g. One selected vector must work simultaneously for every y; its choice is allowed to depend on f and x.

The theorem does not explicitly name the derivative or identify its representing vector with g in the conclusion. That identification may be an intended mathematical consequence, but the displayed target is solely the equivalence of the stated predicates.

## Slot 4: Singleton-to-interior prerequisite

For every such E and extended-valued convex f, every x with a finite real value, and every g in E, if the entire subdifferential of f at x is exactly the singleton {g}, then x is in the ambient topological interior of the effective domain.

This is an implication from an exact singleton assertion, not from nonemptiness alone. It supplies the interior conclusion rather than assuming it. The displayed prerequisite shares the equivalence's convexity and finite-point assumptions. No claim is made here about which proof strategy uses it, since no proof bodies are supplied.

## Slot 5: Explicit and absent assumptions

Finite-dimensionality, real inner product structure, epigraph convexity, and a finite value at the selected point are explicit premises of both statements. Neither statement explicitly assumes properness, exclusion of negative infinity everywhere, lower semicontinuity, closedness of the epigraph, or prior interior membership. The full equivalence therefore cannot be reconstructed as an equivalence restricted in advance to interior points of a proper function.

The finite-point premise excludes both infinities at x but does not by itself exclude negative infinity elsewhere. On the singleton side, global support at the finite-valued point forces exclusion of negative infinity everywhere: the supporting expression is finite at every y and cannot be at most negative infinity. Together with the given finite value, that side implies properness. SourceDifferentiableAt directly supplies a finite-valued neighborhood and hence interior membership; any further global consequence on that side would need the convexity assumption or additional reasoning.

No premise is omitted as unused merely because it may follow under one side of the equivalence. The task is to reconstruct the displayed contracts, not weaken them.

## Slot 6: Ambient interior and extended-real boundaries

Interior is taken in the full norm topology of E, not relative to an affine hull and not within the effective domain as a subspace. The differentiability predicate uses the same ambient neighborhoods. A finite point on a lower-dimensional effective domain with empty ambient interior cannot satisfy SourceDifferentiableAt. The prerequisite asserts that such a point cannot have a singleton subdifferential under the displayed hypotheses either.

Positive-infinity values outside the local finite neighborhood are permitted by the differentiability predicate, and the global supporting inequality is automatically satisfied at such values. A negative-infinity value anywhere would prevent any supporting vector at the chosen finite point. The definition of effectiveDomain itself still includes negative-infinity values; it is the available hypotheses or support consequences, not the definition, that can exclude them.

A finite x ensures a nonempty effective domain, so the empty-effective-domain case cannot instantiate either theorem. E is inhabited by its zero vector. Zero dimension is allowed; no positive-dimensionality premise appears. These targets do not assert the equivalence at points where f(x) is either infinity.

## Slot 7: Context limits and status

The packet contains definitions and theorem signatures with no proof bodies or imports. It should be read as a statement packet rather than taken as evidence that these declarations form a self-contained compilable file. Standard meanings are used for Convex, neighborhood-filter eventual equality, interior, and DifferentiableAt. Their implementations were not inspected.

The claimed equivalence and singleton-to-interior implication are reconstructed as draft contracts. This document supplies no source-fidelity verdict, compilation claim, proof-validity finding, or assertion that these are accepted theorems. It also makes no claim that global support can be replaced by a restricted-domain inequality without changing the contracts.
