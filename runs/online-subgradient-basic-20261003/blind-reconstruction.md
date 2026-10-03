# Source-blind mathematical reconstruction

Actor: `/root/closed_blind`, distinct source-blind decoder assigned GPT-6 Astra medium.

Read inventory for this reconstruction: only `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-basic-20261003/blind-packet.txt`. No imported file, external source, earlier verdict, or other file was inspected for this task. This actor previously completed a separate closed/proper packet reconstruction; that prior assignment did not include source material.

## Ambient setting and definitions

E is any real inner product space with its normed additive commutative group structure. Completeness, finite dimension, openness or closedness of any set, and differentiability are not stated assumptions. In particular E is inhabited by its zero vector.

For every extended-real-valued function f and point x in E, `SourceSubdifferential f x` is the set of vectors g in E such that, for every y in the entire ambient space E,

    f(x) + <g, y - x> <= f(y).

The inner product is a finite real number embedded into EReal. The support inequality is global: y is not restricted to a feasible set, an effective domain, or a neighborhood. The definition itself imposes no convexity, properness, or finite-value condition on f or x. Its arithmetic is extended-real arithmetic; the added inner-product term is always finite, so no addition of opposite infinities occurs in this expression.

`SourceProper f` requires both that f never takes negative infinity and that there exist a point z in E and a finite real r with f(z) = r. Positive infinity elsewhere is allowed.

`effectiveDomain f` is the set {x : f(x) < positive infinity}. As defined, it includes points with value negative infinity. Only in conjunction with the no-negative-infinity condition of SourceProper does membership mean that f(x) is a finite real value. Thus the definition of effectiveDomain by itself is not exactly the finite-valued locus of an arbitrary extended-real function.

## First target: `subgradient_point_finite`

For every such E and every f : E -> EReal, if f is SourceProper, then for every x and g in E, membership of g in SourceSubdifferential f x implies x belongs to effectiveDomain f.

Equivalently, at any point admitting a global supporting vector, a proper extended-real function has a value strictly below positive infinity. Properness also rules out negative infinity, so under the full assumptions its value there is finite. The conclusion is set membership, not an explicit existential real-value equality.

The quantifier order is: choose f; assume its properness; choose x and g; assume the global inequality for that particular pair; conclude f(x) < positive infinity. No convexity assumption is needed or stated. The finite-value witness in properness rules out f(x) = positive infinity: at that witness, adding a finite inner-product term to f(x) would still be positive infinity, which cannot be less than or equal to the witness's finite value.

The no-negative-infinity conjunct is stronger than needed for the literal conclusion f(x) < positive infinity: existence of one finite value already excludes positive infinity at a supporting point. The conjunct is needed to read that conclusion as actual finiteness. If f(x) were negative infinity, every finite inner-product shift would remain negative infinity and the support inequality at x would hold for every g, even for functions not proper. If f were identically positive infinity, every g would also satisfy the inequality at every x, but no x would belong to effectiveDomain; this case fails properness's finite-value witness requirement.

## Second target: `theorem_2_21`

For every real-valued function f : E -> real numbers and every convex subset V of E, if at every x in V there exists a vector g in E globally supporting f at x, then f is convex on V.

Expanded, the support assumption is:

    for every x in V, there exists g in E such that,
    for every y in E, f(x) + <g, y - x> <= f(y).

The same selected g must work for all y, but may depend on x. This is not a single common vector for all x, and is not the weaker quantifier order allowing a different g for each pair (x,y). The function is first embedded pointwise into EReal when applying SourceSubdifferential; because f is real-valued, all function values and support terms in this target are finite. In ordinary real arithmetic the support inequality has the displayed equivalent meaning. The output `ConvexOn real V f` is convexity of the original real-valued function, not an extended-real convexity conclusion.

In the standard meaning of ConvexOn, V is convex and for every u,v in V and real a,b with a >= 0, b >= 0 and a + b = 1,

    f(a*u + b*v) <= a*f(u) + b*f(v).

The convex-set premise ensures that the convex combination belongs to V, where the support assumption is available. A support vector at that combination can be used against u and v. The support assumption nevertheless quantifies globally over y in E even though only comparisons to points of V are needed for convexity on V; it is stronger than the corresponding restricted support condition. No support vector is required at points outside V. No separate properness, lower semicontinuity, closedness of V, or interior-point assumption appears in this theorem. Real-valuedness already supplies finite values everywhere, and E is nonempty.

For V empty, the support assumption is vacuous and the convexity conclusion holds under the standard empty-set convention. For V a singleton, convexity of f on V holds, but the stated global supporting-vector assumption can still be nontrivial because it compares the singleton point with every y outside V. This is a sufficient-condition theorem; no converse is asserted.

## Context limits

The packet gives the three relevant definitions explicitly. Inner-product-space structure and `Convex`/`ConvexOn` are imported rather than expanded; their mathematical readings above are standard and their exact library implementations were not independently inspected. The packet contains an import and then an explicit SourceProper definition; without reading the imported file, this reconstruction cannot determine whether that name is already declared there or whether the packet is a self-contained compilable unit. This is contextual uncertainty only. No source-fidelity verdict, compilation claim, or proof-validity claim is made.
