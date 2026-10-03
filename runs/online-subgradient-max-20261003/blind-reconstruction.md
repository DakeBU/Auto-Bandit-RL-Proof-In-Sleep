# Independent automated blind reconstruction

Reviewer role: source-blind semantic decoder, automated agent; this is not an external human review. The only mathematical input inspected was `blind-packet.txt`. No source, intended source identity, proof body, contract, or other run was inspected. This reconstructs statement semantics; it does not certify a proof or source correspondence.

## Ambient objects and quantifiers

Both claims quantify over an arbitrary type E with a normed additive commutative group and a real inner product space structure. The function values are extended real numbers EReal, allowing negative and positive infinity. Gradients are vectors of E; the support pairing is the real inner product with g in the first argument and y - x in the second. No finite-dimensionality hypothesis occurs in claim_1. Claim_2 additionally requires E to be finite-dimensional over the reals. Completeness is not an explicit assumption.

The index type is arbitrary but has Fintype and Nonempty instances. Thus the family is finite and contains at least one function, with no uniform cardinality bound. Every claim holds for every family f and every point x subject to its displayed hypotheses. Classical choice in the maximum definition supplies any needed decidability; a user-provided DecidableEq instance is not a theorem requirement.

## Definitions decoded

M(x) = max over all indices i of f_i(x). This is the actual maximum of the full finite nonempty family in the extended-real order, implemented by the nonempty finite supremum. It is not a separately supplied upper envelope, supremum bound, or real-valued surrogate. In particular, an index attaining it exists at each point even if that value is an infinity.

The effective domain used here is exactly {x : f(x) < positive infinity}. In isolation it includes points with f(x) = negative infinity. Properness means both that negative infinity is excluded at every point and that at least one point has a real value. Consequently properness together with membership in the effective domain makes the value finite and real.

Extended convexity means convexity over the reals of the real epigraph {(z,t) in E times R : f(z) <= t}, where t is embedded into EReal. There is no closed-epigraph or lower-semicontinuity assumption in this definition.

The subdifferential at x is exactly the set of g in E satisfying f(x) + <g,y-x> <= f(y) for EVERY y in E. The inner product is a real number embedded into EReal before addition. The condition is global, not restricted to a domain, neighborhood, or active indices; no finiteness guard at x is built into this definition.

A(x) is the union, over indices satisfying the exact equality f_i(x) = M(x), of the individual subdifferentials at x. Equivalently g belongs to A(x) precisely when some such active index has g as a global supporting vector. This is a union of sets of vectors, not a union of functions, an intersection of subdifferentials, a sum, or a set of gradients requiring differentiability. Inactive functions contribute no vectors.

## Claim 1: unconditional inclusion

For every ambient real inner product space as above, every finite nonempty family of arbitrary EReal-valued functions, and every x, A(x) is a subset of the subdifferential of M at x.

Expanded: if there exists an index i with f_i(x) = M(x) and, for every y, f_i(x) + <g,y-x> <= f_i(y), then for every y, M(x) + <g,y-x> <= M(y).

This claims only inclusion. It assumes neither convexity, properness, continuity, finite values at x, nor finite-dimensionality. An empty active subgradient union makes the inclusion vacuous. Although an active index always exists, its subdifferential need not be nonempty. The header does not itself state convex-hull inclusion or equality.

## Claim 2: exact convex-hull equality

For every finite-dimensional ambient real inner product space, every finite nonempty family of EReal-valued functions, and every x: assume each f_i is proper and has a convex real epigraph; assume x lies in the effective domain of EVERY f_i; and assume EVERY f_i is continuous at x as a map E -> EReal. Then

    subdifferential M(x) = convexHull over R of A(x).

The continuity assumptions apply to all functions, not just active ones. They are ambient-space continuity at the specified point, not merely continuity relative to an effective domain. Properness is global for each function and its real witness may depend on i; the separate common-domain hypothesis supplies a common finite point x. No hypothesis says the functions are finite everywhere or continuous everywhere.

This is equality of subsets of E and hence both directions, not just the always-valid active-vector inclusion. Every supporting vector of M is a finite convex combination of supporting vectors selected from active functions, and every such combination supports M. ConvexHull denotes the ordinary convex hull, with no closure, closed convex hull, cone, or affine hull. Nonemptiness of the hull is not an additional explicit conclusion of the displayed header.

## Degeneracies and exact scope

- Under claim_2, all f_i(x) and M(x) are real and finite. Claim_1 permits infinities. The subdifferential definition at a negative-infinity value contains every g because adding a finite inner product leaves negative infinity. At a positive-infinity value it contains every g only if the function is positive infinity everywhere, and otherwise it is empty. These facts concern the displayed extended-real support definition, which has no domain guard.
- An empty index family is excluded. A singleton family is permitted: claim_1 reduces to self-inclusion and claim_2 says its subdifferential equals its own convex hull under the assumptions.
- Ties among maximizers are permitted and all tied indices enter the active union. Duplicate functions are permitted. No unique active index is assumed.
- The zero-dimensional ambient space is permitted. No positive dimension, nonzero vector, or nonempty interior is explicitly required.
- Claim_2 does not require differentiability, strict convexity, a Lipschitz constant, compactness, global real-valuedness, or a numerical regularity modulus. Claim_1 does not require any of claim_2's analytic hypotheses.

## Context limitations and ambiguities

The packet labels its imported definitions as mathematical context and says it is not standalone compiled code. The reconstruction therefore takes these displayed definitions as authoritative, without checking actual imported declarations or instance elaboration. ContinuousAt uses the topology supplied for EReal; with the standard EReal topology this is extended-real continuity. The packet does not separately spell out that topology. No proof bodies, proof dependencies, build evidence, or original-source mapping were available, so correctness of implementation and fidelity to an intended external theorem remain outside this blind reconstruction.