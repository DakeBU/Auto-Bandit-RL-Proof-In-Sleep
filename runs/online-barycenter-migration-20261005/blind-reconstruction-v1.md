# Restricted-input reconstruction of N01–N03

This fresh pass read only `blind-packet-v1.md` in this directory as mathematical file input. No source identity, public name map, proof body, prior verdict, or other file was read. Earlier unrelated actor history is retained and is not claimed erased. This is a distinct automated decoder role requested as GPT-6 Astra / medium; it is not a runtime-model attestation or human/external-model review. The input was not modified. No compilation, proof validation, source acceptance, chapter certification, or Goal certification is claimed.

Independent SHA-256 of the packet's exact raw bytes:
`175a3d01d3f3391b5ca2ee2371a18a2ec61e76041d486f6b0ee71b220b2e1c84`.

The three headers have separate sections and different typeclass assumptions. They must not be given a single strengthened common ambient context. Bochner integral, Integrable, almost-everywhere statements, BorelSpace, closure and interior are interpreted mathematically here, not inspected in imported source code. Integrability has its usual Bochner meaning, including the relevant almost-everywhere strong measurability and finite norm integral. A probability measure has total mass one; it supplies the normalization absent for an arbitrary measure. Write m=∫X dμ where that integral occurs.

## N01 — equality of one functional almost everywhere

1. **Objects/spaces:** A measurable space Ω; a real normed space E with normed additive commutative group structure and completeness; a probability measure μ on Ω; X:Ω→E; its Bochner mean m; and a supplied continuous real-linear functional a:E→ℝ. E need not be an inner-product space or finite-dimensional. This section does not explicitly require a MeasurableSpace E or BorelSpace E instance.
2. **Quantifier order:** For every μ with probability-measure instance, every integrable X, and every supplied continuous linear a, if the displayed upper bound holds μ-almost everywhere, the corresponding equality holds μ-almost everywhere. The functional is not existentially selected by this theorem and may depend on previously fixed data; the comparison level is the same fixed real scalar a(m) throughout.
3. **Assumptions:** IsProbabilityMeasure μ; Integrable X μ; and
   \[
   a(X(\omega))\le a(m)\quad\text{for }\mu\text{-almost every }\omega.
   \]
   There is no a≠0 hypothesis, no convex set, and no assumption that X itself is pointwise bounded or constant.
4. **Conclusion/metric:**
   \[
   a(X(\omega))=a(m)\quad\text{for }\mu\text{-almost every }\omega.
   \]
   The scalar projection of X through this single functional is almost surely equal to its value at the mean.
5. **Constants/normalization:** Comparison coefficient one and total mass one; no division by μ(Ω), tolerance, or rate is present. Both sides are ordinary real values of a, not vector norms.
6. **Information/probability:** Both premise and conclusion are almost-everywhere statements relative to the same probability measure. They need not hold at every ω. There is no filtration, temporal information order, independence, or sampling condition.
7. **Boundaries/exclusions:** a=0 is allowed and yields a trivial scalar equality. Equality of a(X) does not assert X=m or that X is constant: variation in directions annihilated by a is not excluded. Completeness is explicit; finite dimensionality, Borel-space structure on E, or a nonzero separator must not be added. A non-normalized arbitrary measure is outside the header unless it separately satisfies the probability instance. No closedness or set-membership conclusion is involved.

## N02 — existence of a nonzero supporting functional

1. **Objects/spaces:** A finite-dimensional real normed space E, convex subset s⊆E, point x∈E, and a continuous real-linear functional a:E→ℝ to be supplied by the conclusion. The section does not explicitly list CompleteSpace E, measurable structures, an inner product, or any measure.
2. **Quantifier order:** For every convex s and point x satisfying the closure and noninterior conditions, there exists one functional a such that a≠0 and, for every y∈s, a(y)≤a(x). The chosen a may depend on s and x but is fixed before quantifying over y.
3. **Assumptions:**
   \[
   s\text{ is convex},\qquad x\in\overline s,\qquad x\notin\operatorname{interior}(s).
   \]
   Interior is ambient topological interior, not relative interior. There is no premise x∈s, no explicit closedness assumption, and no separately written nonemptiness condition.
4. **Conclusion/metric:**
   \[
   \exists a\in\mathcal L(E,\mathbb R):\quad a\ne0\quad\land\quad
   \forall y\in s,\ a(y)\le a(x).
   \]
   Thus a nonzero continuous linear functional supports s at the level through x. The affine hyperplane has equation a(y)=a(x); the functional itself remains linear.
5. **Constants/normalization:** Threshold exactly a(x), with no positive gap or strict separation. Nonzero does not mean unit norm: no normalization such as ‖a‖=1 is asserted. The direction is a(y)≤a(x).
6. **Information/probability:** Deterministic geometric existence. There is no measure or probability context and no assertion that an arbitrary already supplied functional has this property.
7. **Boundaries/exclusions:** x can belong to closure(s) without belonging to s. s need not be closed or full-dimensional. Empty s has empty closure, so no x satisfies its closure premise; a separate nonempty assumption need not be invented. A set with empty ambient interior can still fall within the statement at closure points. In the zero-dimensional space the stated geometric premises have no instance requiring an impossible nonzero functional. No existence of a strictly separating gap or uniqueness of a is claimed. Infinite-dimensional spaces are outside the stated finite-dimensional scope.

## N03 — the mean belongs to the actual convex set

1. **Objects/spaces:** A measurable space Ω (universe v); a finite-dimensional real normed space E (universe u) with explicit MeasurableSpace E and BorelSpace E structure; a probability measure μ; a convex set s⊆E; and X:Ω→E with Bochner mean m. Completeness is not an explicitly listed class in this section, although it is a standard consequence of the finite-dimensional real normed-space setting. No inner-product assumption is present.
2. **Quantifier order:** For every μ satisfying the probability instance, every convex s, and every X satisfying integrability and μ-a.e. membership in that same s, the integral lies in s. The set is fixed in the hypotheses before asserting the resulting membership; no functional is chosen or supplied in this header.
3. **Assumptions:** IsProbabilityMeasure μ; Convex ℝ s; Integrable X μ; and
   \[
   X(\omega)\in s\quad\text{for }\mu\text{-almost every }\omega.
   \]
   The Borel-space context on E is explicitly retained. There is no closedness, openness, boundedness, nonempty-interior, or explicit MeasurableSet s premise. There is no separately supplied everywhere Measurable X hypothesis beyond the actual Integrable condition and its imported semantics.
4. **Conclusion/metric:**
   \[
   m=\int_\Omega X(\omega)\,d\mu(\omega)\in s.
   \]
   This is membership in the actual set s, not merely its closure or closed convex hull.
5. **Constants/normalization:** Total mass one is explicit. The mean is the unscaled Bochner integral because μ is a probability measure. No division by mass, approximation tolerance, or distance-to-set bound is introduced.
6. **Information/probability:** The membership premise is μ-almost everywhere, so exceptional outcomes outside s are permitted on a null set. The conclusion concerns the deterministic integral, not a sample realization or a claim that every outcome lies in s. No independence or information filtration appears.
7. **Boundaries/exclusions:** Nonclosed convex s is allowed and the conclusion is not weakened to closure(s). No conclusion that s itself is closed is licensed. Empty s cannot satisfy a.e. membership under a probability measure, so no contradictory empty-set case is implied. X need not be constant, and no functional-value equality is asserted in this header. Infinite-dimensional spaces or arbitrary unnormalized measures lie outside the displayed assumptions. Neither measurability of s nor an ambient interior point should be added as a hidden requirement.

## Scope limits

All three headers have seven-slot coverage. N01 uses a complete real normed space and any supplied functional; N02 uses finite dimension to assert existence of a nonzero supporting functional from closure/noninterior premises; N03 explicitly adds Borel context and a probability/integrability/a.e.-membership package to conclude actual-set mean membership. These are statement reconstructions only. No imported implementation, proof, source identity, or acceptance evidence was inspected.
