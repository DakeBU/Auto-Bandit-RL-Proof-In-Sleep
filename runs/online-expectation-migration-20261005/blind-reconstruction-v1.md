# Restricted-input reconstruction: N01–N10

This fresh pass read only `blind-packet-v1.md` in this run directory as mathematical file input. No source identity, proof body, public module, prior verdict, or other file was consulted. Prior unrelated actor history remains present and is not claimed erased. This is a distinct automated decoder role, requested GPT-6 Astra / medium, without runtime-model attestation, human review, or external-model review. No input was modified and no compilation, proof validation, source acceptance, chapter certification, or Goal certification is claimed.

Independently calculated SHA-256 of exact raw packet bytes:
`7a4741c339916ebe40e7cc1821936f6d09a9b4621e4fef2231b327c610cf54ca`.

## Shared measure-theoretic interpretation

Ω is an arbitrary type with a measurable-space structure. μ is an arbitrary measure on Ω. No finite-measure, probability-measure, total-mass-one, sigma-finiteness, or nonzero-mass assumption occurs. There is no division by μ(Ω), so these expressions are unnormalized integrals. They become expectations only when an appropriate probability-measure interpretation is supplied separately.

Write P_μ(f)=N01 μ f, M_μ(f)=N02 μ f, and J_μ(f)=N03 μ f. The first two take values in ENNReal=[0,+∞]; the third takes values in EReal. Write ι for the indicated embeddings into EReal, whether of real or extended-nonnegative values as appropriate. For an ordinary real function h, write ιh for its pointwise real embedding.

Under the usual interpretation of the imported conversions, z.toENNReal extracts the nonnegative part of an EReal value: positive finite values are retained, nonpositive values including −∞ become zero, and +∞ remains +∞. ENNReal.ofReal(r) similarly represents max(r,0). These library conventions, the lower Lebesgue integral, EReal subtraction, and Bochner Integrable are interpreted, not implementation-verified here.

The displayed definitions are total formal operations and impose no explicit measurability or integrability assumptions. The lower-integral notation is used even for functions without such hypotheses. One must distinguish this formal availability from an ordinary signed Lebesgue-integral interpretation. In particular, when both P and M are infinite, N03 still denotes a formal EReal subtraction expression, but the packet does not define its exceptional arithmetic value or authorize identifying it with a legitimate signed integral of the form +∞−∞.

## N01 — nonnegative-part lower integral

1. **Objects:** Arbitrary μ and f:Ω→EReal; quantity P_μ(f)∈ENNReal.
2. **Quantifiers:** Defined for every measure and every such function.
3. **Assumptions:** Only the measurable-space structure on Ω. No Measurable, AEMeasurable, Integrable, or finiteness hypothesis is imposed on f.
4. **Conclusion:**
   \[P_\mu(f)=\int^-_\Omega (f(\omega)).\operatorname{toENNReal}\,d\mu(\omega).\]
5. **Constants/normalization:** No probability normalization or mass divisor; output can be any extended-nonnegative value.
6. **Information/probability:** Deterministic integral functional for an arbitrary measure; no random sampling or stochastic independence condition.
7. **Boundary:** Allows +∞ output and pointwise ±∞ inputs. Nonpositive values contribute zero under the usual conversion interpretation. For zero measure, including the unique measure on an empty space, the lower integral is zero under the usual integral convention. Total definability is not an added measurability certificate.

## N02 — negative-part magnitude lower integral

1. **Objects:** Arbitrary μ,f and M_μ(f)∈ENNReal.
2. **Quantifiers:** Every measure and extended-real function.
3. **Assumptions:** No explicit function measurability, integrability, or mass assumption.
4. **Conclusion:**
   \[M_\mu(f)=\int^-_\Omega (-f(\omega)).\operatorname{toENNReal}\,d\mu(\omega).\]
5. **Constants/normalization:** Negation is applied before conversion; this is the nonnegative magnitude of the negative part, not a negative-valued integral. No normalization.
6. **Information/probability:** Deterministic functional, not an expectation unless μ is separately made a probability measure.
7. **Boundary:** Positive values including +∞ contribute zero, while −∞ becomes +∞ before integration under the usual conversion interpretation. M can be infinite. Zero/empty-measure cases give zero under standard imported semantics.

## N03 — total signed-difference expression

1. **Objects:** P_μ(f), M_μ(f), and extended-real J_μ(f).
2. **Quantifiers:** Every μ and f:Ω→EReal.
3. **Assumptions:** None beyond their types; neither part is required finite.
4. **Conclusion:**
   \[J_\mu(f)=\iota(P_\mu(f))-\iota(M_\mu(f)).\]
5. **Constants/normalization:** Difference of the two unnormalized lower integrals, with unit coefficients and EReal subtraction.
6. **Information/probability:** Deterministic total formal definition, no probability or information-order hypothesis.
7. **Boundary:** When both parts are finite it has the finite-difference interpretation. The one-infinite-part regimes need appropriate arithmetic interpretation; N10 explicitly covers infinite positive part and finite negative part. When both are infinite, the expression remains formally defined but no valid ordinary signed-integral value is supplied by this packet. No claim of integrability follows from the definition.

## N04 — positive part for embedded real functions

1. **Objects:** Real function h:Ω→ℝ, its EReal embedding ιh, and ENNReal.ofReal(h).
2. **Quantifiers:** Every μ and every real-valued h.
3. **Assumptions:** No measurable or integrable condition, and no restriction on total measure.
4. **Conclusion:**
   \[P_\mu(\iota h)=\int^-_\Omega\operatorname{ofReal}(h(\omega))\,d\mu.\]
5. **Constants/normalization:** Exact identity of ENNReal quantities; ofReal corresponds to positive truncation, with threshold zero.
6. **Information/probability:** Deterministic conversion identity within the formal lower integrals.
7. **Boundary:** h is pointwise finite but may have an infinite positive-part integral. Negative values are permitted. This identity does not assert measurability, finite integral, or a normalized expectation.

## N05 — negative part for embedded real functions

1. **Objects:** Real h, embedding ιh, and positive truncation of −h.
2. **Quantifiers:** Every μ and h:Ω→ℝ.
3. **Assumptions:** None on measurability, integrability, or signs.
4. **Conclusion:**
   \[M_\mu(\iota h)=\int^-_\Omega\operatorname{ofReal}(-h(\omega))\,d\mu.\]
5. **Constants/normalization:** Exact equality; negative-part magnitude, not the integral of min(h,0). No mass normalization.
6. **Information/probability:** Deterministic identity of formal lower integrals.
7. **Boundary:** Real-valuedness does not ensure the right side is finite. Positive h-values contribute zero under the ofReal interpretation; arbitrary measures are included.

## N06 — integrability makes the positive part finite

1. **Objects:** Real h:Ω→ℝ and P_μ(ιh).
2. **Quantifiers:** Every μ,h for which Integrable h μ holds.
3. **Assumptions:** The actual hypothesis is Bochner Integrable h μ. In its usual interpretation this includes almost-everywhere strong measurability and finite norm integral; it is stronger than merely pointwise finite values or existence of a totalized real integral expression. Strict pointwise Measurable h is not separately demanded.
4. **Conclusion:** \(P_\mu(\iota h)\ne+\infty\). Since the codomain is ENNReal, this is finiteness of that nonnegative quantity.
5. **Constants/normalization:** No explicit finite upper bound is given; only exclusion of the infinity element.
6. **Information/probability:** Deterministic integrability implication for any measure.
7. **Boundary:** The positive part may be zero. μ itself need not be finite. No converse or assertion for nonintegrable h is stated, and the header is about real-valued h rather than arbitrary EReal f.

## N07 — integrability makes the negative part finite

1. **Objects:** Real h and negative-part magnitude M_μ(ιh).
2. **Quantifiers:** Every μ,h satisfying Integrable h μ.
3. **Assumptions:** Actual Bochner integrability, with its usual a.e. measurability and finite norm-integral content; no probability normalization.
4. **Conclusion:** \(M_\mu(\iota h)\ne+\infty\).
5. **Constants/normalization:** Finiteness only, not a numerical bound or zero assertion.
6. **Information/probability:** Deterministic implication; arbitrary measure allowed.
7. **Boundary:** Negative values of h are allowed; zero negative part is allowed. Neither finite measure nor pointwise measurability is an extra header assumption. There is no stated converse or guarantee for a merely real-valued nonintegrable function.

## N08 — equality with the real integral under integrability

1. **Objects:** Real h, J_μ(ιh), and the real Bochner integral ∫h dμ embedded into EReal.
2. **Quantifiers:** Every μ and h:Ω→ℝ with Integrable h μ.
3. **Assumptions:** Bochner integrability, not merely a syntactically defined integral. This prevents both part integrals from being infinite and supplies the relevant a.e. measurability.
4. **Conclusion:**
   \[J_\mu(\iota h)=\iota\!\left(\int_\Omega h(\omega)\,d\mu(\omega)\right).\]
5. **Constants/normalization:** Exact equality, unit coefficients, no division by μ(Ω). The right side is the finite real integral embedded into EReal.
6. **Information/probability:** Deterministic identification with a legitimate signed integral in the integrable real-valued regime. It can be called an expectation only with a separately appropriate probability measure.
7. **Boundary:** Zero function and zero measure included. Nonintegrable functions, extended-real-valued inputs, or both-infinite positive/negative parts are not covered. A default value used by a totalized integral outside integrability must not be used to extend this theorem.

## N09 — almost-everywhere nonnegative branch

1. **Objects:** Arbitrary extended-real f, J_μ(f), P_μ(f), and μ-a.e. order condition.
2. **Quantifiers:** Every μ,f with f(ω)≥0 for μ-almost every ω.
3. **Assumptions:** Only \(\forall^\mu\omega,\ 0\le f(\omega)\). There is no separate measurability, integrability, finite-positive-part, or probability-measure hypothesis.
4. **Conclusion:** \(J_\mu(f)=\iota(P_\mu(f))\).
5. **Constants/normalization:** Nonnegative threshold zero, no normalization or correction term. The conclusion removes the negative-part contribution in this a.e. regime.
6. **Information/probability:** “Almost every” is relative to the arbitrary measure μ, not an assumption of unit total mass. The identity is deterministic and ignores a null exceptional set under the formal integral semantics.
7. **Boundary:** f may take negative or −∞ values on an exceptional null set. +∞ values on a non-null set and P_μ(f)=+∞ are allowed. The resulting identity is not a claim of a finite expectation. Without measurability supplied, retain the formal lower-integral meaning rather than silently adding a classical measurable-function hypothesis.

## N10 — infinite-positive, finite-negative branch

1. **Objects:** Extended-real f with positive and negative-part lower integrals, and J_μ(f).
2. **Quantifiers:** Every μ,f satisfying the two part-integral hypotheses.
3. **Assumptions:** P_μ(f)=+∞ and M_μ(f)≠+∞. No separate measurability or integrability is demanded. M is therefore a finite ENNReal value, possibly zero.
4. **Conclusion:** \(J_\mu(f)=+\infty\) in EReal.
5. **Constants/normalization:** Exact top value; positive part uses ENNReal infinity before embedding. No finite bound or scaling.
6. **Information/probability:** Deterministic extended-arithmetic branch for the defined quantity, with arbitrary μ.
7. **Boundary:** Both-infinite case is explicitly excluded by the negative-part premise. This does not state a symmetric negative-infinite theorem, nor assign a legitimate signed-integral meaning to the both-infinite case. It is not an integrable finite-expectation result.

## Scope limits

All three definitions N01–N03 and seven unproved headers N04–N10 have seven-slot coverage. The packet defines total expressions without general measurability premises, while N06–N08 explicitly require actual real Bochner integrability. N09 retains only a.e. nonnegativity and N10 exactly the stated infinite-positive/finite-negative branch. No hidden probability normalization or resolution of the both-infinite signed-integral ambiguity has been added. Imported conventions remain interpretations, not inspected implementations or proof evidence.
