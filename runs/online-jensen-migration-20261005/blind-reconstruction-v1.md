# Restricted current-packet reconstruction of N01–N02

This pass read only `blind-packet-v1.md` in this directory as mathematical file input. It did not inspect source identity, original-name maps, imported definitions, actual named proofs, prior verdicts, or other files. This is restricted current-packet reconstruction, not fresh-history blinding: the actor's prior unrelated history is not erased or claimed absent. The distinct automated decoder is `/root/normal_blind`, requested GPT-6 Astra / medium; no runtime-model attestation, human review, or external-model review is claimed. No compilation, proof validation, source acceptance, chapter certification, or Goal certification is supplied.

Independent SHA-256 of the exact raw packet bytes:
`9cd3bc317281f57767383674f953d6324c5deb92d475577cc36cead0f14ba96e`.

## Common context and supplied-notation boundary

Ω has a measurable-space structure. E is a finite-dimensional real normed space with its normed additive commutative group structure and with explicit MeasurableSpace E and BorelSpace E instances. No inner product is required. CompleteSpace E is not explicitly listed, although completeness is a standard consequence of the finite-dimensional real normed setting. The assertions do not state an infinite-dimensional extension.

The packet supplies the following meanings for named imported predicates and operations: D_f=effectiveDomain(f) is the below-top domain {x:f(x)<+∞}; IsConvexExtended(f) denotes convexity of the real-height epigraph; positiveIntegral and negativeIntegral are total nonnegative-part integrals; signedExpectation is their EReal difference. These meanings are notation supplied by the formalizer. They are not independently decoder-inspected definitions or verified implementations. In particular this report does not claim to have checked imported exceptional arithmetic or total-integral conventions.

Using that supplied notation, put Y(ω)=f(X(ω)), P=positiveIntegral(μ,Y), N=negativeIntegral(μ,Y), and S=signedExpectation(μ,Y), interpreted as the EReal difference of the embedded P and N. Write m=∫X dμ for the vector Bochner integral. The genuine hypothesis Integrable X μ must be retained: the mere existence of a totalized formal integral expression, possibly with a fallback outside integrability, is not a substitute. Likewise, integrability of X does not itself state integrability of Y.

## N01 — finiteness of the negative part of the composed loss

1. **Objects/spaces:** A probability measure μ on measurable Ω; a measurable extended-real f:E→EReal on the finite-dimensional real normed Borel space E; a measurable vector-valued X:Ω→E; the composed loss Y=f∘X; and its nonnegative extended-valued negative-part integral N. No real scalar loss representative or derivative is involved.
2. **Quantifier order:** For every μ with IsProbabilityMeasure μ, every f satisfying its global hypotheses, and every X satisfying its measurability, integrability and μ-a.e. domain conditions, the negative-part conclusion holds. There is no existential choice of f, X, measure, or truncation. The domain condition ranges over almost every ω for that same μ.
3. **Assumptions:** All of the following are explicitly present:
   - μ is a probability measure, with total mass one.
   - ∀x∈E, f(x)≠−∞; this is global, not merely along X.
   - IsConvexExtended(f), interpreted only according to the supplied epigraph notation.
   - Measurable f and Measurable X as separate hypotheses.
   - Integrable X μ, the actual vector Bochner-integrability condition.
   - X(ω)∈D_f for μ-almost every ω.
   These last two hypotheses have different roles and neither can be replaced by the formal availability of ∫X dμ.
4. **Conclusion/metric:**
   \[
   \operatorname{negativeIntegral}(\mu,f\circ X)\ne+\infty.
   \]
   In the supplied nonnegative-integral interpretation, the magnitude of the negative part has finite integral. This is a result, not an additional premise on the loss.
5. **Constants/normalization:** No numerical finite upper bound is specified; the conclusion excludes the infinity element of the nonnegative extended codomain. The probability mass-one premise is retained. No division by μ(Ω), error term, or convergence rate appears.
6. **Information/probability:** This is a deterministic measure-theoretic implication. Domain membership is μ-almost everywhere, not pointwise: exceptional outcomes with X outside D_f are permitted on a null set. Combined with global no-bottom and the supplied below-top meaning, Y is finite almost everywhere. Both strict measurability assumptions remain explicit even though Integrable carries additional usual almost-everywhere measurability content. No independence, filtration, sampling, or temporal-adaptation requirement occurs.
7. **Boundaries/exclusions:** The positive-part integral P can still be +∞; neither real-valued loss integrability nor a finite signed expectation is concluded. N can be zero. f may be +∞ outside its domain, including at exceptional sampled outcomes, but is nowhere −∞ under the global hypothesis. There is no assumption of domain closedness, lower semicontinuity, differentiability, nonempty ambient interior, full dimension, or boundedness. No nonempty-domain premise is written separately; the probability and a.e. domain assumptions rule out an everywhere empty domain under the supplied interpretation. Arbitrary non-normalized measures, nonintegrable vector inputs, and infinite-dimensional spaces are not covered by this header.

## N02 — extended-real convex mean inequality

1. **Objects/spaces:** The same probability μ, extended-real measurable convex-epigraph f, measurable and integrable vector X, mean m∈E, and S=signedExpectation(μ,f∘X) in EReal. The left side is the original extended-real value f(m), not a toReal conversion or an integral of a chosen real extension.
2. **Quantifier order:** For every μ,f,X satisfying the listed common hypotheses, the comparison holds for their actual vector mean. No comparator, supporting functional, auxiliary neighborhood, or minimizer is an extra quantified input or output. The loss-composition expectation on the right belongs to this same μ,f,X.
3. **Assumptions:** Exactly the same hypotheses as N01: probability mass one; global no-bottom for f; named epigraph convexity; Measurable f; Measurable X; genuine Integrable X μ; and μ-a.e. membership of X in D_f. No assumption Integrable (f∘X) μ, finiteness of P, finiteness of N, or pre-existing signed-integral finiteness is written in this header. N01's negative-part finiteness is a separate stated result under these premises, not a hidden new assumption.
4. **Conclusion/metric:**
   \[
   f\!\left(\int_\Omega X(\omega)\,d\mu(\omega)\right)
   \le \operatorname{signedExpectation}(\mu,\omega\mapsto f(X(\omega))).
   \]
   This is an EReal-valued comparison between the loss at the vector mean and the supplied signed part-integral expression of the loss, with inequality in that direction.
5. **Constants/normalization:** Unit coefficients and exact bound, with no additive slack or rate. The vector mean is the unscaled Bochner integral because μ is a probability measure. The right-hand operation is the supplied difference of nonnegative part integrals; no unmentioned averaging by measure mass is inserted.
6. **Information/probability:** Measurability of both f and X is explicitly required, and the domain condition is only almost everywhere. Integrability of X makes m a genuine integrable-vector mean, not a totalized fallback. Under the supplied notation and the separately stated N01, the negative part is finite, so the problematic both-infinite positive/negative regime is excluded for these inputs. This observation is a reading of the two supplied statements, not verification of their proofs. There is no assertion that X is constant or independent of another variable, and no filtration or online information structure.
7. **Boundaries/exclusions:** The signed loss on the right may be +∞ if the positive-part integral is infinite; the conclusion must not be rewritten as a finite real expectation inequality without additional loss-integrability evidence. With both parts finite it has the usual finite signed-integral interpretation. Global no-bottom excludes f(m)=−∞, but this header by itself does not explicitly state m∈D_f or a separate finite-value assertion for f(m); such a stronger barycenter fact must not be silently presented as this header's conclusion. The theorem has no closedness, lower-semicontinuity, full-dimensional-domain, ambient-interior, or differentiability premise. Points outside D_f may have +∞ values. The assumptions are probability-normalized and finite-dimensional; no arbitrary-measure or infinite-dimensional extension is claimed.

## Interpretation limits

All seven semantic slots are covered for both unproved headers. The distinctions retained are vector integrability versus loss integrability, almost-everywhere domain membership versus pointwise membership, supplied global no-bottom versus unspecified properness conventions, a concluded finite negative part versus an assumed finite expectation, and a possibly infinite EReal right side versus an automatically finite real value. Imported names are interpreted only through the packet's supplied notation. No implementation, proof, source correspondence, or acceptance evidence was inspected.
