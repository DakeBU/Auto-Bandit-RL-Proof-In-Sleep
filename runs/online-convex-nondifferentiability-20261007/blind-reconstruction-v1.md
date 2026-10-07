# Neutral blind reconstruction

Only `blind-packet-v1.md` was read. The packet presents one actual definition and three elaborated prospective propositions. It supplies no proved theorem bodies. The seven slots below explicitly record the ambient setting, objects, quantifiers, hypotheses/domain restrictions, assertion, differentiability/boundary semantics, and evidence/scope limits separately for each item.

## Definition Q

Natural language: On the real Euclidean plane, Q assigns to a point the absolute value of its first coordinate.

LaTeX: \(Q:\mathbb R^2\to\mathbb R,\quad Q(x_0,x_1)=|x_0|.\)

1. **Ambient setting:** `EuclideanSpace ℝ (Fin 2)`, the real two-dimensional space with its Euclidean L2 norm.
2. **Objects:** A total real-valued function Q; Lean coordinate 0 is the first coordinate and coordinate 1 the second.
3. **Quantifiers:** The defining equation applies to every point \((x_0,x_1)\in\mathbb R^2\).
4. **Hypotheses/domain restrictions:** None; the domain is the whole plane and both coordinates range over all real numbers.
5. **Assertion:** The value is exactly \(|x_0|\), independent of \(x_1\).
6. **Differentiability/boundary semantics:** The definition alone asserts no differentiability property and contains no restriction to a segment. Values are actual real numbers, without an extended-real conversion.
7. **Evidence/scope limits:** This is an actual supplied definition. It does not itself prove any of P1, P2, or P3 and makes no stochastic, algorithmic, feedback, or regret claim.

## Prospective proposition P1

Natural language: Q is convex on the whole real Euclidean plane.

LaTeX: \(\operatorname{ConvexOn}_{\mathbb R}(\mathbb R^2,Q)\). Equivalently, the domain is convex and, for every \(u,v\in\mathbb R^2\) and \(a,b\geq0\) with \(a+b=1\),
\[
 Q(au+bv)\leq aQ(u)+bQ(v).
\]

1. **Ambient setting:** The same real Euclidean plane; convexity is over scalar field \(\mathbb R\).
2. **Objects:** The defined Q and the universal set `Set.univ`.
3. **Quantifiers:** All pairs of points in the plane and all nonnegative real convex-combination coefficients summing to one.
4. **Hypotheses/domain restrictions:** Only the coefficient conditions in the convexity definition; neither point has a coordinate constraint.
5. **Assertion:** The universal domain is convex and Q satisfies the convexity inequality there.
6. **Differentiability/boundary semantics:** P1 has no differentiability assertion. Its domain is the entire plane, not a segment or axis.
7. **Evidence/scope limits:** P1 is an elaborated proposition of type `Prop`, not a supplied proof. No source identification, acceptance, or chapter completion follows from it.

## Prospective proposition P2

Natural language: Q fails to be differentiable in the ambient real Euclidean plane at every point whose first coordinate is zero. Its second coordinate is unrestricted.

LaTeX:
\[
 \forall x\in\mathbb R^2,\quad x_0=0\Longrightarrow
 \neg\operatorname{DifferentiableAt}_{\mathbb R}(Q,x),
\]
or equivalently \(\forall t\in\mathbb R,\ \neg\operatorname{DifferentiableAt}_{\mathbb R}(Q,(0,t))\).

1. **Ambient setting:** Real Euclidean two-space with its L2 norm, using real Frechet differentiability.
2. **Objects:** Q and an arbitrary point x; the locus is the entire second-coordinate axis \(\{(0,t):t\in\mathbb R\}\).
3. **Quantifiers:** Every x in the plane, conditionally on its first coordinate being zero; equivalently every real second coordinate t.
4. **Hypotheses/domain restrictions:** The sole pointwise premise is \(x_0=0\). There is no interval premise on \(x_1\).
5. **Assertion:** No ambient real Frechet derivative of Q exists at any such x.
6. **Differentiability/boundary semantics:** This is `DifferentiableAt`, not `DifferentiableWithinAt`, a derivative along the axis, or a derivative of a restriction. Although Q restricted to the axis is constant, that restricted-function observation is not the predicate asserted here.
7. **Evidence/scope limits:** P2 is prospective and not furnished with a proof. It asserts nondifferentiability on the entire axis; it does not state an iff characterization or make a claim about other points.

## Prospective proposition P3

Natural language: Q is convex on the whole real Euclidean plane, and Q is not ambiently differentiable at every point of the closed segment from (0,0) to (0,1), including both endpoints.

LaTeX: With \(S=\{(0,t):0\leq t\leq1\}\),
\[
 \operatorname{ConvexOn}_{\mathbb R}(\mathbb R^2,Q)
 \ \land\
 \forall x\in S,\quad\neg\operatorname{DifferentiableAt}_{\mathbb R}(Q,x).
\]
The segment also has the coefficient description
\(S=\{a(0,0)+b(0,1):a,b\in\mathbb R,\ a,b\geq0,\ a+b=1\}\).

1. **Ambient setting:** The same real Euclidean plane, with convexity and Frechet differentiation over \(\mathbb R\).
2. **Objects:** Q, the universal convexity domain, zero vector, and `PiLp.single 2 1 1`, which is (0,1). The segment connects these two distinct vectors.
3. **Quantifiers:** The convexity conjunct has the universal convexity quantifiers described in P1. The second conjunct universally quantifies every x belonging to the specified segment, equivalently every real \(t\in[0,1]\).
4. **Hypotheses/domain restrictions:** Segment membership restricts only the nondifferentiability quantifier. Convexity remains on the whole plane. The second conjunct requires \(x=(0,t)\) with \(0\leq t\leq1\).
5. **Assertion:** Both global convexity and ambient nondifferentiability at all points of that segment hold as a conjunction.
6. **Differentiability/boundary semantics:** The segment is closed, including (0,0) and (0,1). Nondifferentiability concerns Q on the full ambient plane at these points, including the endpoints; it is not failure of differentiability of the constant restriction to the segment. P3's nondifferentiability quantifier does not cover the rest of the axis; P2 does.
7. **Evidence/scope limits:** This is a third prospective proposition, not an already established theorem body. It contains no source attribution, source acceptance, runtime attestation, chapter/Goal completion, or stochastic/algorithmic conclusion.

## Receipt boundary

Actor task: `/root/nondiff_blind`. Requested model: GPT6Astra. Requested effort: medium. These record requested settings only and do not attest to the actual runtime model. Verdict: `blind-reconstructed`. This report reconstructs the packet's mathematical content without reviewing a source or proving its prospective propositions.