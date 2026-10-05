Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this packet in this pass. No source identity, theorem-name map, prior verdict, proof body or other file. Five definitions are mathematical context. Reconstruct Q0-Q4 and M01-M22 in seven slots:objects,quantifiers,assumptions,conclusions,constants/normalization,information/probability,boundary. Missing proof bodies are intentional; no compilation/source acceptance claim. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json beside this packet, with exact raw input/report SHA, actor/requested medium, prior history not erased, sole input this pass and no human/external review.

```lean
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
open Set
namespace Neutral


variable {E : Type*} [AddCommGroup E] [Module ℝ E]


def Q0 (f : E → EReal) : Set E := {x | f x < ⊤}


def Q1 (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}


def Q2 (f : E → EReal) : Prop := Convex ℝ (Q1 f)


def Q3 (V : Set E) (x : E) : EReal := by
  classical
  exact if x ∈ V then 0 else ⊤


def Q4 (a b : EReal) : EReal := -(-a + -b)

theorem M01 (V : Set E) : Convex ℝ V ↔ ∀ x ∈ V, ∀ y ∈ V, ∀ θ : ℝ, 0 < θ → θ < 1 → θ • x + (1 - θ) • y ∈ V

theorem M02 (f : E → EReal) (hf : Q2 f) : Convex ℝ (Q0 f)

theorem M03 (V : Set E) : Q0 (Q3 V) = V

theorem M04 (V : Set E) : Q2 (Q3 V) ↔ Convex ℝ V

theorem M05 (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) : Q1 f = {p : E × ℝ | p.1 ∈ Q0 f ∧ (f p.1).toReal ≤ p.2}

theorem M06 (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) : Q2 f ↔ ConvexOn ℝ (Q0 f) (fun x => (f x).toReal)

theorem M07 (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hdom : Convex ℝ (Q0 f)) : Q2 f ↔ ∀ x ∈ Q0 f, ∀ y ∈ Q0 f, ∀ θ : ℝ, 0 < θ → θ < 1 → f (θ • x + (1 - θ) • y) ≤ (θ : EReal) * f x + ((1 - θ : ℝ) : EReal) * f y

theorem M08 (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hf : Q2 f) (V : Set E) (hV : Convex ℝ V) : Q2 (fun x => f x + Q3 V x)

theorem M09 {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) : Q2 (fun x => (f x : EReal)) ↔ ConvexOn ℝ univ f

theorem M10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : E) (b : ℝ) : Q2 (fun x => ((inner ℝ z x + b : ℝ) : EReal))

theorem M11 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : Q2 (fun x : E => ((‖x‖ : ℝ) : EReal))

theorem M12 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] (f : F → EReal) (hf : Q2 f) (A : E →ᵃ[ℝ] F) : Q2 (fun x => f (A x))

theorem M13 {ι E : Type*} [AddCommGroup E] [Module ℝ E] (f : ι → E → EReal) (hf : ∀ i, Q2 (f i)) : Q2 (fun x => ⨆ i, f i x)

theorem M14 {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) (g : ℝ → ℝ) (hf : Q2 (fun x => (f x : EReal))) (hg : Q2 (fun x => (g x : EReal))) (hmono : Monotone g) : Q2 (fun x => (g (f x) : EReal))

theorem M15 (a b : ℝ) : Q4 (a : EReal) (b : EReal) = ((a + b : ℝ) : EReal)

theorem M16 (a : EReal) : Q4 a ⊤ = ⊤

theorem M17 (a : EReal) : Q4 ⊤ a = ⊤

theorem M18 (a b : EReal) (h : ℝ) : Q4 a b ≤ (h : EReal) ↔ ∃ r s : ℝ, a ≤ (r : EReal) ∧ b ≤ (s : EReal) ∧ r + s ≤ h

theorem M19 {E : Type*} [AddCommGroup E] [Module ℝ E] (f g : E → EReal) (hf : Q2 f) (hg : Q2 g) : Q2 (fun x => Q4 (f x) (g x))

theorem M20 (a : ℝ) (ha : 0 < a) (z : EReal) (h : ℝ) : (a : EReal) * z ≤ (h : EReal) ↔ z ≤ ((h / a : ℝ) : EReal)

theorem M21 {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) (hf : Q2 f) (a : ℝ) (ha : 0 ≤ a) : Q2 (fun x => (a : EReal) * f x)

theorem M22 {E : Type*} [AddCommGroup E] [Module ℝ E] (f g : E → EReal) (hf : Q2 f) (hg : Q2 g) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Q2 (fun x => Q4 ((a : EReal) * f x) ((b : EReal) * g x))

end Neutral
```
