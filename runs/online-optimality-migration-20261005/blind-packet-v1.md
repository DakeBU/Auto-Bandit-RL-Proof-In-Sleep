Fresh restricted-input reconstruction GPT-6 Astra / medium. Read ONLY this packet this pass; no source identity/names/proofs/prior verdict/other files. Four actual unproved headers/imported scoped complete Hilbert context neutralized. Reconstruct seven semantic slots per target, canonical conversion on finite set/neighborhood, ambient versus within derivative/interior, candidate membership versus IsMinOn comparison, all-feasible criterion/boundary and gradientzero extra condition. Imported semantics are interpretation, not inspected implementation. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with sole-current-input packet/report SHA, prior history not erased, no compilation/source/human/external/runtime attestation claim.

```lean
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set Filter
open scoped Topology
namespace Neutral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem M01 (V : Set E) (f : E → ℝ) (hf : ConvexOn ℝ V f) (x : E) (hx : x ∈ V) (hd : DifferentiableAt ℝ f x) : IsMinOn f V x ↔ ∀ y ∈ V, 0 ≤ inner ℝ (gradient f x) (y - x)

theorem M02 (f : E → EReal) (V : Set E) (x : E) (hx : x ∈ V) (hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥) : IsMinOn f V x ↔ IsMinOn (fun z => (f z).toReal) V x

theorem M03 (f : E → EReal) (V U : Set E) (hV : Convex ℝ V) (hne : V.Nonempty) (x : E) (hx : x ∈ V) (hU : IsOpen U) (hVU : V ⊆ U) (hfin : ∀ z ∈ U, f z ≠ ⊤ ∧ f z ≠ ⊥) (hf : ConvexOn ℝ V (fun z => (f z).toReal)) (hd : DifferentiableOn ℝ (fun z => (f z).toReal) U) : IsMinOn f V x ↔ ∀ y ∈ V, 0 ≤ inner ℝ (gradient (fun z => (f z).toReal) x) (y - x)

theorem M04 (f : E → EReal) (V U : Set E) (hV : Convex ℝ V) (hne : V.Nonempty) (x : E) (hx : x ∈ V) (hxi : x ∈ interior V) (hU : IsOpen U) (hVU : V ⊆ U) (hfin : ∀ z ∈ U, f z ≠ ⊤ ∧ f z ≠ ⊥) (hf : ConvexOn ℝ V (fun z => (f z).toReal)) (hd : DifferentiableOn ℝ (fun z => (f z).toReal) U) : IsMinOn f V x ↔ gradient (fun z => (f z).toReal) x = 0

end Neutral
```
