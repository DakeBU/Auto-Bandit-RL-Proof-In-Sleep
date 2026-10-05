Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this packet this pass, no source/public-name map/proof bodies/prior verdict/other files. Q0/Q1/Q2 definitions and M01/M02/M03 unproved actual headers, complete scoped context. Reconstruct all six objects in seven semantic slots; retain local versus global finite-part facts, interior point, global noBottom, all-y bound, derivative-at-point and full real ConvexOn helper hypotheses. Imported gradient/toReal conventions are interpretations, not inspected runtime definitions. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with exact raw packet/report SHA, sole input currentpass, prior history not erased, no compilation/source/human/external/runtime attestation claim.

```lean
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.EReal.Basic
noncomputable section
open Set Filter
open scoped Topology
namespace Neutral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
def Q0 (f : E → EReal) : Set E := {x | f x < ⊤}
def Q1 (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
def Q2 (f : E → EReal) : Prop := Convex ℝ (Q1 f)

theorem M01 (f : E → EReal) (hbot : ∀ z, f z ≠ ⊥) (x : E) (hx : x ∈ interior (Q0 f)) : ∀ᶠ z in 𝓝 x, ((f z).toReal : EReal) = f z

theorem M02 (V : Set E) (f : E → ℝ) (hf : ConvexOn ℝ V f) (x y : E) (hx : x ∈ V) (hy : y ∈ V) (hd : DifferentiableAt ℝ f x) : f x + inner ℝ (gradient f x) (y - x) ≤ f y

theorem M03 (f : E → EReal) (hbot : ∀ z, f z ≠ ⊥) (hf : Q2 f) (x : E) (hx : x ∈ interior (Q0 f)) (hd : DifferentiableAt ℝ (fun z => (f z).toReal) x) (y : E) : f x + ((inner ℝ (gradient (fun z => (f z).toReal) x) (y - x) : ℝ) : EReal) ≤ f y

end Neutral
```
