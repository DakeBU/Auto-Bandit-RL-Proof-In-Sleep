# Blind statement reconstruction: zero_curvature_affine_has_no_minimum

Scope: interpretation of this packet's authorized header and definition context only. No source, imports, proofs, reviews, or Lean execution. No provider-use, proof-validity, or source-acceptance claim.

Verified SHA256: declaration-v1.txt = a1eedbc4618df9b0b1328b1668cb0ea45aafbc29ab7a3710acfb7d1eb6f99886; definition-context-v1.txt = 910e6e40db16c31ac9a4660ee5e83b575aaf8c74f5e2ffbc583497def61b2191.

## Ambient definitions and binders

E=EuclideanSpace ℝ (Fin 1), the real Euclidean line. point(t) is the vector with sole coordinate t. Norm and scalar multiplication are Euclidean; the real inner product is coordinate multiplication. Write A=affine, where A(x)=(x 0:EReal). Every A(x) is finite. D=effectiveDomain A is defined by A(x)<top, hence D is all E. The context's coordinates map is the identity algebraic linear equivalence, and its quadratic function is a halfline-restricted squared function; neither occurs in this proposition.

There are no external parameters, instance binders, or hypothesis arrows. This is a closed proposition with five right-associated top-level conjuncts. SourceProper internally contains a conjunction, and the curvature and no-minimum clauses internally contain quantifiers, but these do not change the top-level count. All five clauses are asserted facts of this particular function, not assumptions provided to a general theorem.

## Five conjuncts in exact order

1. SourceProper A. Expanded: (∀ x:E, A(x)≠bottom) AND ∃ x:E, ∃ r:ℝ, A(x)=(r:EReal). The definition is everywhere finite, with point(0) and r=0 giving a finite witness.
2. SourceClosed A. For every r:ℝ, {x:E | A(x)≤(r:EReal)} is closed. These are exactly the coordinate halflines {x | x 0≤r} in the Euclidean topology. No separate LowerSemicontinuous predicate is displayed.
3. For every x∈D, every y∈D, and every a:ℝ satisfying 0<a and a<1,

   A(a • x+(1-a) • y) ≤ (a:EReal)*A(x) + ((1-a:ℝ):EReal)*A(y) - ((((0:ℝ)/2)*a*(1-a)*‖x-y‖²:ℝ):EReal).

   Quantifiers occur as x, membership, y, membership, a, strict lower bound, strict upper bound. The norm is the ambient Euclidean norm. The real correction coefficient is zero, so the subtracted EReal term is zero. All objective values are finite; the inequality simplifies to the affine identity, hence equality. This asserts zero curvature, not strictly positive strong convexity.
4. point(1)∈SourceSubdifferential A (point(0)). Expanded: ∀ z:E, A(point(0))+(inner ℝ (point(1)) (z-point(0)) embedded in EReal)≤A(z). Both sides equal the embedded coordinate z 0. This is a global supporting vector at the specified point, with vector point(1), not a zero-vector optimality certificate.
5. ¬(∃ p:E, ∀ q:E, A(p)≤A(q)). There exists no global minimizer over all E. The existential variable p is inside negation; q is universally quantified inside the existential's predicate. Equivalently every candidate has a strictly better comparator in the extended-real total order. Concretely, a point with coordinate p 0-1 has smaller objective value. No effective-domain membership is included in this final existential; every point is already finite and in D.

## Meaning and edge cases

This particular proper, real-sublevel-closed affine function has a global subgradient at point(0) and satisfies the zero-curvature inequality, yet has no attained global minimum. The real coordinate objective is unbounded below, but no point has bottom value. Thus failure of attainment does not contradict properness, and it does not arise from a top or bottom evaluation at any point.

The declaration contains no strictly positive curvature parameter, compact feasible region, toReal conversion, indicator, operator norm, or division by curvature. The only displayed division is 0/2 in ℝ, whose denominator is the nonzero constant 2. There is no zero-denominator quotient in this statement. Interior weights a∈(0,1) are the ones explicitly quantified.

No pointwise minimum value is claimed, finite or infinite. No general assertion that all zero-curvature functions lack minima is claimed. The statement provides one fixed example and cannot contradict an existence theorem with a strictly positive curvature assumption. It does not assert how any theorem was proved, whether a provider was invoked, or any algorithmic consequence.

## Ambiguities and evidence limits

The enclosing namespace is absent from the input, so only the short theorem name is recoverable. Given the supplied definitions, the logical scopes and top-level conjunction count are unambiguous. Internal implementations and proof bodies were not inspected. The header alone cannot establish compilation, proof correctness, proof dependencies, or source faithfulness.
