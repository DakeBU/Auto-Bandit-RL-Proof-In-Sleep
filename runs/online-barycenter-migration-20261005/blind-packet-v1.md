Fresh restricted reconstruction GPT-6 Astra / medium. Read ONLY this packet this pass; no source identity/names/proof bodies/verdicts/other files. Three unproved headers with actual separate section/import/type contexts neutralized. Reconstruct seven slots per target; separate normed complete versus finite-dimensional scopes, explicit Borel context, probability/Integrable/AE membership, ambient interior/closure versus actual-set mean, nonzero separator versus supplied arbitrary functional, no X-constant/closedness inference. Imported semantics are interpretation, not inspected implementation. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with sole current packet/report SHA; history not erased/no compilation/source/human/external/runtime attestation.

```lean
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open Set Filter MeasureTheory
universe u v
namespace Neutral

section SupportEquality
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem N01 (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Integrable X μ) (a : E →L[ℝ] ℝ) (hle : ∀ᵐ ω ∂μ, a (X ω) ≤ a (∫ ω, X ω ∂μ)) : ∀ᵐ ω ∂μ, a (X ω) = a (∫ ω, X ω ∂μ)
end SupportEquality

section FiniteSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem N02 (s : Set E) (hs : Convex ℝ s) (x : E) (hx : x ∈ closure s) (hxi : x ∉ interior s) : ∃ a : E →L[ℝ] ℝ, a ≠ 0 ∧ ∀ y ∈ s, a y ≤ a x
end FiniteSupport

section Barycenter
variable {Ω : Type v} [MeasurableSpace Ω]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem N03 (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set E) (hs : Convex ℝ s) (X : Ω → E) (hX : Integrable X μ) (hmem : ∀ᵐ ω ∂μ, X ω ∈ s) : (∫ ω, X ω ∂μ) ∈ s
end Barycenter

end Neutral
```
