import BanditRLProof.OnlineConvexFirstOrder
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set Filter
open scoped Topology
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem minOn_real_iff_gradient (V : Set E) (f : E → ℝ) (hf : ConvexOn ℝ V f)
    (x : E) (hx : x ∈ V) (hd : DifferentiableAt ℝ f x) :
    IsMinOn f V x ↔ ∀ y ∈ V, 0 ≤ inner ℝ (gradient f x) (y - x) := by
  constructor
  · intro h y hy
    simpa using h.localize.hasFDerivWithinAt_nonneg
      hd.hasGradientAt.hasFDerivAt.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hf.1.segment_subset hx hy))
  · intro h y hy
    change f x ≤ f y
    have hl := convex_gradient_lower_bound V f hf x y hx hy hd
    have hn := h y hy
    linarith

theorem minOn_finitePart_iff (f : E → EReal) (V : Set E) (x : E) (hx : x ∈ V)
    (hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥) :
    IsMinOn f V x ↔ IsMinOn (fun z => (f z).toReal) V x := by
  have hxfin := EReal.coe_toReal (hfin x hx).1 (hfin x hx).2
  constructor
  · intro h y hy
    have hyfin := EReal.coe_toReal (hfin y hy).1 (hfin y hy).2
    have hh : f x ≤ f y := h hy
    change (f x).toReal ≤ (f y).toReal
    rw [← hxfin, ← hyfin] at hh
    exact_mod_cast hh
  · intro h y hy
    have hyfin := EReal.coe_toReal (hfin y hy).1 (hfin y hy).2
    change f x ≤ f y
    rw [← hxfin, ← hyfin]
    have hh : (f x).toReal ≤ (f y).toReal := h hy
    exact_mod_cast hh

theorem theorem_2_8 (f : E → EReal) (V U : Set E) (hV : Convex ℝ V)
    (hne : V.Nonempty) (x : E) (hx : x ∈ V) (hU : IsOpen U) (hVU : V ⊆ U)
    (hfin : ∀ z ∈ U, f z ≠ ⊤ ∧ f z ≠ ⊥)
    (hf : ConvexOn ℝ V (fun z => (f z).toReal))
    (hd : DifferentiableOn ℝ (fun z => (f z).toReal) U) :
    IsMinOn f V x ↔ ∀ y ∈ V, 0 ≤ inner ℝ (gradient (fun z => (f z).toReal) x) (y - x) := by
  have hd' := (hd x (hVU hx)).differentiableAt (hU.mem_nhds (hVU hx))
  exact (minOn_finitePart_iff f V x hx (fun z hz => hfin z (hVU hz))).trans
    (minOn_real_iff_gradient V (fun z => (f z).toReal) hf x hx hd')

theorem interior_min_iff_gradient_zero (f : E → EReal) (V U : Set E) (hV : Convex ℝ V)
    (hne : V.Nonempty) (x : E) (hx : x ∈ V) (hxi : x ∈ interior V)
    (hU : IsOpen U) (hVU : V ⊆ U) (hfin : ∀ z ∈ U, f z ≠ ⊤ ∧ f z ≠ ⊥)
    (hf : ConvexOn ℝ V (fun z => (f z).toReal))
    (hd : DifferentiableOn ℝ (fun z => (f z).toReal) U) :
    IsMinOn f V x ↔ gradient (fun z => (f z).toReal) x = 0 := by
  constructor
  · intro h
    have hr := (minOn_finitePart_iff f V x hx (fun z hz => hfin z (hVU hz))).mp h
    have hl := hr.isLocalMin (mem_interior_iff_mem_nhds.mp hxi)
    simp [gradient, hl.fderiv_eq_zero]
  · intro h
    apply (theorem_2_8 f V U hV hne x hx hU hVU hfin hf hd).mpr
    intro y hy
    simp [h]

end BanditRL.OnlineConvex
