# Source-blind reconstruction: interior support

Actor: `/root/closed_blind`, distinct decoder assigned GPT-6 Astra / medium. No proof editing.

Read inventory: only `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-interior-20261003/blind-packet.txt`, read as text and hashed as file bytes.

Packet SHA256: `B202CF04D82A8DB3129609375FF234DF7E9D0E8EC07EDD918EDC9FE98283690D`.

Prior exposure: this actor previously decoded the separate closed/proper and basic-subgradient packets in this conversation. Those packets exposed related definitions and theorem targets. No external source text, source identification search, prior source-review verdict, or other repository file was read for this assignment. Thus this is source-blind but not independent of all earlier mathematical context.

## Slot 1: Mathematical objects and definitions

The first statement concerns an arbitrary finite-dimensional real normed vector space E and a function f from E into the extended reals. The second concerns an arbitrary finite-dimensional real inner product space F and such a function on F.

The effective domain is {x : f(x) < positive infinity}. Without other assumptions this includes negative-infinity values. The real epigraph is the set of pairs (x,t) with x in the ambient space, t a finite real number, and f(x) <= t. Convexity of this subset of the real product vector space is the stated definition of extended convexity. Properness means that f never equals negative infinity and takes a finite real value at some point.

The subdifferential at x is the set of vectors g satisfying f(x) + <g,y-x> <= f(y) for every y in the whole ambient inner product space. The inner-product term is finite and is embedded into the extended reals.

## Slot 2: Assumptions and scope

The affine-support theorem assumes a normed additive commutative group structure, a real normed-space structure, finite dimension over the reals, exclusion of negative infinity at every point, convexity of the real epigraph, and membership of the selected point x in the topological interior of the effective domain. An inner product is not an assumption of this first theorem. It does not explicitly assume properness or separately assume existence of a finite value.

The subgradient-existence theorem assumes a normed additive commutative group, a real inner product structure, finite dimension over the reals, properness, convexity of the real epigraph, and interior membership of x. The inner product supplies the relevant real normed-space structure implicitly.

Neither statement explicitly assumes lower semicontinuity, closedness of the epigraph, differentiability, or nonempty interior as a separate global premise: the chosen x witnesses the last condition. No auxiliary feasible set appears.

## Slot 3: Quantifier order and first conclusion

For every allowed E and f, under the stated no-negative-infinity and convexity hypotheses, and for every selected x satisfying interior membership, there exist a continuous real-linear functional a : E -> real numbers and a finite real scalar b such that BOTH:

1. The embedded finite real a(x)+b equals f(x).
2. For every y in all of E, the embedded finite real a(y)+b is at most f(y).

The same a and b must satisfy contact at x and the inequality simultaneously for every y. They may depend on f and x; no one affine function supporting at every x is asserted. The bound is global, including points outside the effective domain. The contact condition is equality, not merely an inequality or an approximate contact condition. Continuity is part of the stated type of a.

## Slot 4: Quantifier order and second conclusion

For every allowed F and f, given properness and epigraph convexity, and for every x in the interior of the effective domain, there exists g in F such that for every y in F,

    f(x) + <g,y-x> <= f(y).

Thus the selected g works globally for all y; it may depend on x. Nonemptiness of the set of subgradients is the exact conclusion, not uniqueness, a bound on their norms, continuity of a selection, or differentiability. Contact is implicit in this definition: at y=x the finite inner product is zero and the support expression equals f(x). Since the assumptions make f(x) finite, it describes a real affine supporting function anchored at (x,f(x)).

## Slot 5: Infinity and finiteness boundaries

Interior membership implies effective-domain membership, so f(x) < positive infinity. The exclusion of negative infinity then makes f(x) finite. Consequently the first theorem already entails existence of a finite value and hence properness; its explicitly weaker-looking assumptions supply the witness through x. In the second theorem the finite-value-existence conjunct of properness is redundant given x's interior membership and the no-negative-infinity conjunct, although properness is the actual stated hypothesis and should not be omitted when reporting that statement.

Values of positive infinity away from x are allowed. At such a point the global finite affine lower bound is automatically at most f(y). Negative-infinity values anywhere are excluded; a finite affine lower bound could not hold at such a point. The real epigraph has no points above an argument with value positive infinity; above a finite-valued argument its vertical fiber is the corresponding upper real ray. Under the hypotheses it never has the full real fiber produced by a negative-infinity value.

The identically-positive-infinity function has empty effective domain and cannot supply the required x, even though its empty real epigraph is convex. The theorem does not infer a subgradient for such a function.

## Slot 6: Interior, topology, and domain boundaries

The interior is the ambient norm-topological interior in E or F. It is not relative interior inside an affine hull and is not a condition imposed in a restricted domain topology. If the effective domain is lower-dimensional with empty ambient interior, neither theorem applies at any point of it, even if its relative interior is nonempty. A point merely on the boundary of the effective domain is not covered unless it also happens to satisfy the actual interior premise; no general boundary-point existence conclusion is asserted.

The ambient vector spaces are inhabited by zero. Dimension zero is not excluded. No positive-dimensionality premise appears. The chosen interior point, rather than any blanket assumption on dimension, is what supplies nonemptiness of the effective domain.

## Slot 7: Interpretation limits and possible unused assumptions

All definitions needed for the extended-valued interpretation are provided in the packet. Convexity, interior, continuous linear maps, and the inner product rely on imported standard mathematical notions; their implementations were not inspected. The first theorem uses a real normed space rather than an inner product space; the second specifically asserts a representing vector in an inner product space. This is a meaningful distinction in their conclusions.

The finite-value witness in the second theorem's properness assumption is logically recoverable from other stated assumptions, as explained above. No other assumption is classified as unused from the statement alone. In particular finite-dimensionality is an explicit premise even if analogous results might be available in other settings. No proof bodies were supplied, so proof-level dependency or unused-argument claims are unavailable. This document makes no external-source fidelity verdict, compilation claim, or proof-validity claim.
