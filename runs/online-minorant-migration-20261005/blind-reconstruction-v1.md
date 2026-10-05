# Restricted-input reconstruction of N01–N04

This fresh pass used only `blind-packet-v1.md` in this directory as mathematical file input. No source, target-name map, imported predicate body, proof, prior verdict, or other file was inspected. Prior unrelated actor history is not erased or claimed absent. The actor is a distinct automated decoder requested as GPT-6 Astra / medium, without runtime-model attestation or human/external-model review. No input was modified. No compilation, proof validation, source acceptance, chapter completion, or Goal completion is claimed.

Independent SHA-256 of exact raw packet bytes:
`ca4d2588864c378b1d0eb87ec3e327bad879dbe46c9abaded4ec1f376367996c`.

## Common context and imported-predicate boundary

Every header uses a finite-dimensional real normed space E with normed additive commutative group and NormedSpace ℝ structures. No inner-product structure, measurable-space structure, BorelSpace, or probability measure is supplied. CompleteSpace is not an explicitly listed hypothesis. The finite-dimensional setting has its usual completeness consequences, but no extension to arbitrary infinite-dimensional spaces is stated. The namespace openings do not themselves add measure-theoretic assumptions.

The packet imports the named predicates `IsConvexExtended` and `effectiveDomain` but does not reproduce their definitions. This pass therefore retains them exactly as named assumptions. For mathematical readability only, the intended interpretation is extended-real convexity, and a below-top effective domain, respectively. In formulas below write C_ext(f)=IsConvexExtended f and D_f=effectiveDomain f. If D_f is the usual {y:f(y)<+∞}, then no-bottom together with membership implies a finite real value. This identification, and an epigraph-convex interpretation of C_ext, were not checked from definitions in this pass and must not be cited as inspected code or independently verified semantics.

Write ι(r) for the EReal embedding of r∈ℝ. A witness a:E→L[ℝ]ℝ is a continuous real-linear functional. With b∈ℝ, the function ℓ(y)=a(y)+b is everywhere finite and affine. There is no a≠0 or norm normalization in any conclusion. Zero linear functional, hence a constant affine function when it satisfies the bound, is permitted. No header assumes differentiability of f or states that a is its gradient.

All lower bounds below compare against every ambient y∈E, not merely the effective domain. Under the usual EReal order interpretation, a finite affine value is below +∞, but not below −∞. No lower-semicontinuity, closed epigraph, or closed-domain property is asserted or assumed explicitly. The eventual statement in N01 is a neighborhood-filter statement, not a time or probability limit.

## N01 — touching affine support from neighborhood finiteness

1. **Objects/spaces:** f:E→EReal on the finite-dimensional real normed E, point x∈E, and existential continuous linear functional a plus real offset b.
2. **Quantifier order:** For every f satisfying C_ext(f), and every x with the specified local condition, there exist a,b, fixed for that f,x, satisfying both equality at x and a bound for every y∈E. The witness pair is selected before the universal query y.
3. **Assumptions:** C_ext(f) and
   \[
   \forall^{\mathrm{eventually}}y\text{ in }\mathcal N(x),\quad
   \exists r\in\mathbb R,\ f(y)=\iota(r).
   \]
   This means finite-real values throughout some neighborhood of x, not just one finite value at x. The real witness may depend on y; no common value, uniform magnitude bound, or differentiability is required. There is **no explicit global no-bottom premise** in this header.
4. **Conclusion/metric:**
   \[
   \exists a\in\mathcal L(E,\mathbb R)\ \exists b\in\mathbb R:\quad
   \iota(a(x)+b)=f(x)\ \land\
   \forall y\in E,\ \iota(a(y)+b)\le f(y).
   \]
   Thus the finite affine lower bound touches f at the prescribed point x.
5. **Constants/normalization:** Exact equality at x and non-strict global lower bound, with coefficient one on both a(y) and b. No approximation error, positive separation gap, or unit-norm condition.
6. **Information/probability:** Deterministic local-to-global support statement. Neighborhood “eventually” is topological; no almost-everywhere or probability condition appears. No constructive algorithm for finding a,b is supplied.
7. **Boundaries/exclusions:** Mere finiteness at one point does not match the neighborhood premise. The premise excludes either infinity locally, including at x, but does not explicitly forbid −∞ everywhere as an additional assumption; the asserted global finite lower bound itself would exclude any bottom value if the conclusion holds. +∞ away from the neighborhood is compatible with the bound. The functional can be zero. No closedness, lower semicontinuity, gradient, or infinite-dimensional generalization is included.

## N02 — touching support at an ambient effective-domain interior point

1. **Objects/spaces:** Extended-real f, its named effective domain D_f, point x in the ambient interior of D_f, and a,b defining a finite affine function on E.
2. **Quantifier order:** For every f under the global hypotheses and each qualifying x, there exist a,b that touch at that x and bound f for every ambient y. Witnesses may depend on x but not on the subsequent query y.
3. **Assumptions:** ∀y∈E, f(y)≠−∞; C_ext(f); x∈interior(D_f). Interior is ambient topological interior, not relative or intrinsic interior. Under the intended below-top domain interpretation, these hypotheses provide local finite-real values; this interpretation was not body-checked here.
4. **Conclusion/metric:**
   \[
   \exists a,b:\quad \iota(a(x)+b)=f(x)
      \ \land\ \forall y\in E,\ \iota(a(y)+b)\le f(y),
   \]
   with a continuous real-linear and b real. This is touching support at the given x, not only existence of some lower bound elsewhere.
5. **Constants/normalization:** Exact tangency in value, non-strict lower bound, no normalized or nonzero functional requirement.
6. **Information/probability:** Deterministic geometric existence. Global no-bottom is explicitly supplied here, unlike N01. There is no probability, sampling, or information-order condition.
7. **Boundaries/exclusions:** A point merely in D_f or on its ambient boundary need not satisfy the interior premise. If D_f has empty ambient interior, there is no admissible x for this statement. +∞ outside D_f remains allowed under the intended semantics. Neither loss differentiability, lower semicontinuity, nor closedness is demanded; zero a is allowed.

## N03 — global affine minorant under the same interior hypotheses

1. **Objects/spaces:** f, D_f, the supplied interior point x, and existential continuous linear a and scalar b.
2. **Quantifier order:** For every f and x satisfying all listed hypotheses, there exists a single a,b whose lower-bound inequality holds for every y∈E.
3. **Assumptions:** Global no-bottom ∀y, f(y)≠−∞; C_ext(f); x∈interior(D_f). These assumptions still mention a specific ambient interior point even though x does not occur in the conclusion.
4. **Conclusion/metric:**
   \[
   \exists a\in\mathcal L(E,\mathbb R)\ \exists b\in\mathbb R,
   \quad\forall y\in E,\ \iota(a(y)+b)\le f(y).
   \]
   This is existence of an everywhere finite affine minorant only.
5. **Constants/normalization:** Coefficient one and non-strict comparison; a may be zero, b arbitrary subject to the bound.
6. **Information/probability:** Deterministic existence with a fixed witness pair for all y. It does not specify a computation or a measure-theoretic exceptional set.
7. **Boundaries/exclusions:** No equality at x, no contact point anywhere, and no gradient identification is included in this weaker conclusion, even though N02 separately states more under matching assumptions. Empty ambient interior still prevents application. The explicit no-bottom premise is global and must not be dropped. No inferred closedness or lower semicontinuity.

## N04 — global affine minorant from nonempty effective domain

1. **Objects/spaces:** f on finite-dimensional real normed E, named domain D_f, and existential affine lower function a(·)+b.
2. **Quantifier order:** For every f satisfying the global premises and D_f.Nonempty, there exist a,b such that the bound holds for all x∈E. There is no prescribed candidate point in the header, and no interior point is quantified as an input.
3. **Assumptions:** ∀x, f(x)≠−∞; C_ext(f); and D_f is nonempty. Nonemptiness means existence of some member of the imported effective domain. Under the intended below-top interpretation plus no-bottom, that is a finite-real witness; no body inspection established that identification in this pass.
4. **Conclusion/metric:**
   \[
   \exists a\in\mathcal L(E,\mathbb R)\ \exists b\in\mathbb R,
   \quad\forall x\in E,\ \iota(a(x)+b)\le f(x).
   \]
   This is a global finite affine lower bound with no asserted attainment or touching equality.
5. **Constants/normalization:** Arbitrary real offset b and possibly zero a; neither normalization nor quantitative lower-bound constant is specified in advance.
6. **Information/probability:** Deterministic existence. No measure, measurability, Borel structure, random selection, or algorithmic information condition is present.
7. **Boundaries/exclusions:** Ambient interior need not be nonempty. In particular lower-dimensional or singleton effective domains are not excluded by the stated nonemptiness condition. Empty D_f is excluded; both-infinite or global no-bottom failures do not meet the premises. Under the intended interpretation, +∞ may occur away from the finite domain. The conclusion does not assert closedness of the domain/epigraph, lower semicontinuity, existence of a minimizer, a contact point, or a nonzero supporting functional. No infinite-dimensional extension is supplied.

## Interpretation limits

All four unproved headers have seven-slot coverage. The crucial differences are the genuine neighborhood finiteness in N01 without an explicit global no-bottom premise, the ambient interior/no-bottom hypotheses in N02–N03, the touching conclusion in N01–N02 versus only a minorant in N03–N04, and mere nonempty domain in N04. Imported project predicates remain uninterrogated names with stated intended interpretations. This report does not establish that those interpretations equal their source definitions or that any theorem has a valid proof.
