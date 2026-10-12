# Independent blind reconstruction: stronglyConvex_existsUnique_minimizer

## Scope and verified inputs

Only this packet's authorized `declaration-v1.txt` and `definition-context-v1.txt` were used to reconstruct this statement. No proof, imported module, external source, review, or other packet is used as evidence. No Lean execution occurred. This is a header interpretation, not a proof-validity, compilation, or source-acceptance finding.

- declaration-v1.txt SHA256: 543e702b86e738dbc5c1a47eba555d6e05f261f4ada1bc67a99edcdf0d0a76ad
- definition-context-v1.txt SHA256: 62e25fe95c839337217ce0e5de2d8c00e6999f2be5663cea57834e125dd3a4e3

## All binders in order

1. Implicit E : Type*.
2. Instance NormedAddCommGroup E.
3. Instance NormedSpace ℝ E.
4. Explicit d : ℕ.
5. Explicit e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d).
6. Explicit f : E → EReal.
7. Explicit lam : ℝ.
8. Explicit hf : SourceProper f.
9. Explicit hclosed : SourceClosed f.
10. Explicit hlam : 0 < lam.
11. Explicit hstrong, the quantified inequality below.
12. Explicit hsub, the nonempty set of points with a nonempty coordinate subdifferential below.

The theorem is universal over these inputs satisfying the hypotheses. The type of e is a REAL LINEAR EQUIVALENCE, not an isometry or a continuous-linear-equivalence type. It asserts an invertible linear coordinate identification with the finite-dimensional real Euclidean space of dimension d. No equality of the given E norm with the transported Euclidean norm is assumed. E itself has a normed-space structure here, not an explicitly supplied inner-product-space structure.

## Hypotheses expanded

Let D={x:E | f(x)<top}. SourceProper means BOTH

- for every x:E, f(x)≠bottom;
- there exist x:E and r:ℝ such that f(x)=(r:EReal).

Together these make D nonempty and make each value f(x), x∈D, a finite embedded real. SourceClosed means that for every real r, {x:E | f(x)≤(r:EReal)} is closed in the norm topology on E. The header does not separately bind LowerSemicontinuous f.

The scalar lam is a strictly positive real. For every x∈D, every y∈D, and every a:ℝ with 0<a and a<1, hstrong asserts

    f(a • x + (1-a) • y)
      ≤ (a:EReal)*f(x) + ((1-a:ℝ):EReal)*f(y)
          - (((lam/2)*a*(1-a)*‖x-y‖²:ℝ):EReal).

The quantifier order is x, domain membership, y, domain membership, a, positivity, strict upper bound. This is an EReal inequality. The coefficient and norm square are formed in ℝ and then cast. The squared norm is the GIVEN AMBIENT NORM ON E. Only interior weights are explicitly required. The right side is finite because x,y∈D and SourceProper excludes bottom. Therefore these interior convex combinations have finite values as a consequence, and D is convex after including the trivial endpoints. Convexity of D is not a separate binder.

To expand hsub, put F(u)=f(e.symm(u)) on EuclideanSpace ℝ (Fin d). The premise is exactly

    ∃ p:E, ∃ g:EuclideanSpace ℝ (Fin d),
      ∀ u:EuclideanSpace ℝ (Fin d),
        f(p) + ((inner g (u - e(p)) : ℝ) : EReal) ≤ f(e.symm(u)).

Here e.symm(e(p))=p supplies the displayed simplification. The outer set is the set of p:E whose coordinate subdifferential at e(p) is nonempty; its Nonempty makes p existential, and the inner Nonempty makes the supporting vector g existential. This is support at AT LEAST ONE point, not a support vector at every point. The inner product and the support vector are in the Euclidean coordinate space, and the support inequality is global over all u, not just finite-domain u.

The hsub predicate does not explicitly include p∈D or finite f(p). Nevertheless that finiteness follows from SourceProper: a finite-valued point exists, so if f(p) were top the global support inequality at its coordinate image would compare top plus a finite real with a finite real, which is impossible. Bottom is independently excluded by SourceProper. This is a logical consequence of the supplied premises, not an extra assumption in hsub. No premise says that the witnessing support vector is zero.

## Exact conclusion and uniqueness scope

The conclusion is

    ∃! p:E, p∈D ∧ ∀ q:E, f(p)≤f(q).

Thus there exists exactly one point p in the effective domain that globally minimizes f over ALL of E. Expanded, there is p with that conjunction, and every p':E satisfying that same conjunction equals p. The minimum has a finite real value because p∈D and SourceProper excludes bottom. The comparator q is unrestricted and may have f(q)=top. Uniqueness is among points satisfying the complete predicate, and any global minimizer would also have finite value because a finite point exists and bottom is excluded.

No prescribed compact feasible set is part of this statement. It asserts existence and uniqueness, not a formula for the minimizer, a rate, a bound on its location, an algorithm, or a particular support witness at the minimizer.

## Edge cases, distinctions, and ambiguities

- d=0 is allowed. The coordinate space then has one vector and e forces E to be linearly equivalent to that zero-dimensional space. No d>0 premise appears.
- E is nonempty as a normed additive group. The effective domain cannot be empty because SourceProper supplies a finite point.
- f may be top outside its effective domain but is nowhere bottom. There is no claim that f is finite everywhere.
- lam=0 and lam<0 are excluded. There is no reciprocal of lam or division-by-zero issue; lam/2 divides by the fixed nonzero real 2.
- No toReal, finite prefix sum, indicator, or operator norm appears in this declaration. It uses ambient E norm and coordinate Euclidean inner product in distinct roles.
- The linear equivalence supplies a finite-dimensional setting. Its type does not assert metric preservation; no proof using such preservation is licensed by this header.
- SourceSubdifferential is explicitly defined in the supplied context, so the reconstruction does not silently add a finite-basepoint side condition to that definition.
- The short theorem name is supplied without an enclosing namespace; the fully qualified name is undetermined. The implementation bodies of SourceProper, SourceClosed, and SourceSubdifferential were not consulted; the supplied semantic definitions are the interpretation boundary. There is no material ambiguity in the displayed quantifier scopes.

The statement does not show how existence or uniqueness is proved, whether hsub is used by a proof, which provider/helper theorem is invoked, or whether the header matches any external source. Those questions cannot be answered from these inputs.
