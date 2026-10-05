Fresh restricted-input reconstruction, GPT-6 Astra / medium. Read ONLY this packet this pass: no source identity, proof bodies, source verdicts or other files. Three actual definitions and seven unproved headers neutralized. Reconstruct seven slots, arbitrary-measure versus probability/normalization, total definitions versus legitimate signed-integral meaning, both-infinite boundary, actual Integrable assumption and a.e. nonnegativity/infinite-positive branch. Imported semantics may be interpreted, not claimed inspected. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json here with sole-current-input packet/report SHA; prior history not erased; no source/compilation/human/external/runtime attestation.

```lean
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace Neutral
variable {Ω : Type*} [MeasurableSpace Ω]

def N01 (μ : Measure Ω) (f : Ω → EReal) : ℝ≥0∞ :=
  ∫⁻ ω, (f ω).toENNReal ∂μ

def N02 (μ : Measure Ω) (f : Ω → EReal) : ℝ≥0∞ :=
  ∫⁻ ω, (-f ω).toENNReal ∂μ


def N03 (μ : Measure Ω) (f : Ω → EReal) : EReal :=
  (N01 μ f : EReal) - (N02 μ f : EReal)

theorem N04 (μ : Measure Ω) (f : Ω → ℝ) : N01 μ (fun ω => (f ω : EReal)) = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ

theorem N05 (μ : Measure Ω) (f : Ω → ℝ) : N02 μ (fun ω => (f ω : EReal)) = ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ

theorem N06 (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) : N01 μ (fun ω => (f ω : EReal)) ≠ ∞

theorem N07 (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) : N02 μ (fun ω => (f ω : EReal)) ≠ ∞

theorem N08 (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) : N03 μ (fun ω => (f ω : EReal)) = ((∫ ω, f ω ∂μ : ℝ) : EReal)

theorem N09 (μ : Measure Ω) (f : Ω → EReal) (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω) : N03 μ f = (N01 μ f : EReal)

theorem N10 (μ : Measure Ω) (f : Ω → EReal) (hp : N01 μ f = ∞) (hn : N02 μ f ≠ ∞) : N03 μ f = ⊤
end Neutral
```
