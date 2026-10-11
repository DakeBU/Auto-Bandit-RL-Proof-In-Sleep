# Independent blind statement reconstruction, version 1

Status: statement reconstruction only; not acceptance, proof checking, or source comparison. Only the two named neutral inputs were read. No theorem proof, imported implementation, source book, proposed correspondence, or prior verdict was consulted.

## Exact inputs

- `declaration-v1.txt`: SHA-256 `6b3937a683760c04d44a0fe595490aa3a12ead49ee490eaca534670c641d3b7f`.
- `notation-v1.txt`: SHA-256 `8da7fdf49d2079c19845f7f7a2dbc9609d98fee006a26f7b8f73c144a6f174ff`.

The declaration hash matches the requested hash. The input does not name a canonical list of seven semantic slots; the seven numbered slots below explicitly partition its complete mathematical content without inferring any intended source statement.

## The seven semantic slots

1. **Ambient objects and coordinates.** Universally fix a real normed vector space E, an integer d >= 0, and an algebraic real-linear bijection e: E -> R^d, with inverse e^(-1). Here R^d means EuclideanSpace real (Fin d) with its standard inner product. The norm on E is the norm from E's given NormedAddCommGroup/NormedSpace structure. The declaration does not equip E with an inner product and does not assert that e preserves norms or inner products. Existence of e entails that E has finite real dimension d. Finite dimensionality makes linear maps continuous in these norms, but continuity or norm preservation is not a separate premise here.

2. **Function and global properness.** Universally fix f: E -> [-infinity,+infinity]. Assume SourceProper f: for every x in E, f(x) != -infinity, and there exists some x in E and some real r with f(x) = r. This does not make f finite everywhere and does not assert global convexity. The existential finite-value witness is not explicitly required to lie in V.

3. **Set, convexity, and finite values on it.** Universally fix V subset E and assume V is convex over the reals. Assume V subset effectiveDomain f, where effectiveDomain f = {x : f(x) < +infinity}. By itself this effective-domain definition includes -infinity values; global properness excludes them. The two assumptions together imply that f is finite and real-valued at every point of V. Nonemptiness of V is not a separate set premise, but the later selected p in V supplies it in every instantiated conclusion.

4. **Curvature parameter and strong-convexity inequality.** Universally fix a real lambda >= 0. Assume, for every x,y in V and every real a with 0 < a < 1,

   f(a x + (1-a)y) <= a f(x) + (1-a) f(y) - (lambda/2) a(1-a) ||x-y||_E^2.

   This is written using extended-real arithmetic and finite-real coercions in the declaration. Convexity keeps the interpolated point in V, where every participating f-value is finite, so it also has the usual real-valued interpretation. The assumption quantifies only over strict interior coefficients a; it does not explicitly quantify over a = 0 or a = 1. Its curvature term uses the original norm on E, not the coordinate Euclidean norm. No strong convexity is assumed for pairs outside V.

5. **Base point.** Fix any p in E with p in V. In particular f(p) is finite. No relative-interior, interior, differentiability, or minimizer condition is imposed on p.

6. **Coordinate subgradient and global support.** Fix any g in R^d satisfying membership in SourceSubdifferential F at e(p), where F(u) = f(e^(-1)(u)). By the supplied definition this means, for every u in R^d,

   F(e(p)) + <g, u-e(p)> <= F(u).

   The pairing is a finite real number coerced into EReal before addition. Since e is a linear bijection, the same premise says, for every z in E,

   f(p) + <g, e(z-p)> <= f(z).

   This is global support: the quantifier covers all of E, including points outside V. It is not merely support on V or on a neighborhood of p. At points where f(z) = +infinity the comparison imposes no restriction; at every point with finite f(z) it is an ordinary supporting-affine-function inequality. There are no -infinity points under properness. The linear functional on E represented by g is z |-> <g,e(z)>; g itself is a coordinate-space vector. This premise is assumed; the declaration does not prove existence of such a g or nonemptiness of the subdifferential.

7. **Comparison point and asserted growth.** For any q in E with q in V, the asserted conclusion is the real inequality

   (f(p)).toReal + <g,e(q-p)> + (lambda/2) ||q-p||_E^2 <= (f(q)).toReal.

   Because p,q lie in V, their toReal values are precisely their finite real values, with no infinity-conversion artifact. Equivalently, f(q) >= f(p) + <g,e(q-p)> + (lambda/2)||q-p||_E^2, interpreted in the reals at p and q. The theorem adds quadratic growth to the assumed linear support for targets q in V. It does not assert this quadratic inequality for targets outside V.

## Quantifier order and what is supplied

The binder order is: E and its real normed-space structures; d; e; f; V; lambda; properness of f; convexity of V; V's domain inclusion; nonnegativity of lambda; the universally quantified strong-convexity premise; p; membership p in V; g; global subgradient membership at e(p); q; membership q in V; then the displayed conclusion. All ordinary objects are universally quantified, with the listed hypotheses supplied conditionally. The finite-value witness inside properness is existential. The x,y,a quantifiers in strong convexity and the u quantifier in subgradient membership are universal and internal to their respective premises.

For every fixed admissible p and every fixed admissible g, the result holds for every q in V: one support vector works for all such q. It is not a statement of the form 'for every q there exists g'. The theorem neither constructs p nor constructs g. If V is empty, no p-membership premise can be instantiated; if the global subdifferential at a chosen p is empty, no g-membership premise can be instantiated.

Properness, convexity, domain inclusion, nonnegative lambda, the strong-convexity inequality, the two memberships in V, and subgradient membership are hypotheses. Finiteness of f on V, nonemptiness of V after supplying p, and the equivalent support statement on E follow from those hypotheses and definitions. The quadratic support inequality is the theorem's asserted conclusion. This reconstruction does not establish that conclusion by a Lean proof or verify its typechecking.

## Norm and pairing must remain separate

In both the assumed curvature inequality and the concluded growth inequality, ||.||_E is E's original norm. The separate linear term uses the standard Euclidean inner product after applying e to the displacement. There is no license to replace ||q-p||_E by ||e(q-p)||_2, nor to write <g,q-p> as an inner product on E without additional definitions. The coordinate transformation represents a linear functional; it does not change the norm controlling curvature. A different coordinate bijection can require a different vector representing the same functional.

## Boundary cases and limits

- **d = 0:** R^0 has a single vector, and bijectivity makes E a singleton. The supplied p forces V to contain that sole point; q = p and g = 0. Both displacement terms vanish and the conclusion is equality. Every lambda >= 0 is compatible with the curvature inequality in this case. The declaration does not require positive dimension.
- **lambda = 0:** The curvature premise reduces to the strict-coefficient convexity inequality on V. The conclusion reduces to the already-assumed supporting-affine inequality at q. Positive quadratic growth and strict convexity are not obtained from lambda = 0.
- **q = p:** The conclusion is equality for every admissible lambda and g.
- **Outside V:** Global linear support still applies, but the theorem's quadratic improvement is not stated there. Values +infinity outside V are permitted; no global finiteness, global strong convexity, lower semicontinuity, closedness of V, or global convexity is supplied.
- **Existence and optimization:** Existence of subgradients, minimizers, or an optimizing algorithm is not asserted. If a supplied admissible g equals zero, the conclusion does imply p minimizes f on V, and positive lambda excludes a different minimizer in V; these are conditional consequences, not existence assertions or separate conclusions in the declaration.
- **Regularity and uniqueness:** The statement does not assert differentiability or uniqueness of the support vector. Its choice of arbitrary norm on E and arbitrary algebraic coordinates must be retained.

No mathematical notation ambiguity remains after using the supplied neutral definitions. The only organizational ambiguity is the unspecified naming of the seven requested slots, resolved by the explicit partition above. No source identity or intended theorem correspondence was inferred.
