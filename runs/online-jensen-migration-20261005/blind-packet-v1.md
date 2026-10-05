Required restricted reconstruction GPT-6 Astra/medium. Read ONLY this packet in this pass; no source identity/numbered original names/prior verdicts/other files/proof bodies. Two neutral unproved headers, exact imports/scoped context. Interpret named imported predicates only from their names and supplied neutral notation, explicitly flag that their actual definitions were NOT independently inspected. Reconstruct seven slots including probability normalization, AE domain membership, global no-bottom, genuine Integrable vector versus total Bochner fallback, finite negative part versus assumption, possibly +infinite signed loss. FiniteD real normed/Borel scope, no loss-integrability/closedness/lsc/full-dimensional-domain hypothesis. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json in this run with sole packet/report SHA and reading boundary/history not erased; no compilation/source/human/external/runtime attestation.

Neutral notation: effectiveDomain is the below-top domain; IsConvexExtended names convexity via a real-height epigraph. positiveIntegral/negativeIntegral name total nonnegative part integrals; signedExpectation names their EReal difference. These are notation supplied by the formalizer, not decoder-inspected bodies.

```lean
import BanditRLProof.OnlineExpectation
import BanditRLProof.OnlineConvexMinorant

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace Neutral
variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

open BanditRL.OnlineConvex

theorem N01 (μ : Measure Ω) [IsProbabilityMeasure μ] (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hf : IsConvexExtended f) (hfm : Measurable f) (X : Ω → E) (hXm : Measurable X) (hX : Integrable X μ) (hdom : ∀ᵐ ω ∂μ, X ω ∈ effectiveDomain f) : negativeIntegral μ (fun ω => f (X ω)) ≠ ∞

theorem N02 (μ : Measure Ω) [IsProbabilityMeasure μ] (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hf : IsConvexExtended f) (hfm : Measurable f) (X : Ω → E) (hXm : Measurable X) (hX : Integrable X μ) (hdom : ∀ᵐ ω ∂μ, X ω ∈ effectiveDomain f) : f (∫ ω, X ω ∂μ) ≤ signedExpectation μ (fun ω => f (X ω))

end Neutral
```
