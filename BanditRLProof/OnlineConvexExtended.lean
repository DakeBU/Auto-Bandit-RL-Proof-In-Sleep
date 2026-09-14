import Mathlib.Analysis.Convex.Function
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

noncomputable section
open Set

namespace BanditRL.OnlineConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Source effective domain includes negative infinity and excludes positive infinity. -/
def effectiveDomain (f : E → EReal) : Set E := {x | f x < ⊤}

/-- Epigraph heights are real, as in the source subset of R^(d+1). -/
def realEpigraph (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- Definition 2.3 permits both infinite function values. -/
def IsConvexExtended (f : E → EReal) : Prop := Convex ℝ (realEpigraph f)

/-- Extended-real constraint indicator, distinct from the zero-outside Set.indicator. -/
def extendedIndicator (V : Set E) (x : E) : EReal := by
  classical
  exact if x ∈ V then 0 else ⊤

theorem definition_2_2 (V : Set E) : Convex ℝ V ↔
    ∀ x ∈ V, ∀ y ∈ V, ∀ θ : ℝ, 0 < θ → θ < 1 → θ • x + (1 - θ) • y ∈ V := by
  rw [convex_iff_forall_pos]
  constructor
  · intro h x hx y hy θ hθ hθ1
    exact h hx hy hθ (sub_pos.mpr hθ1) (by ring)
  · intro h x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst b
    exact h x hx y hy a ha (by linarith)

theorem convex_effectiveDomain (f : E → EReal) (hf : IsConvexExtended f) :
    Convex ℝ (effectiveDomain f) := by
  intro x hx y hy a b ha hb hab
  have hpx : (x, (f x).toReal) ∈ realEpigraph f := EReal.le_coe_toReal (ne_of_lt hx)
  have hpy : (y, (f y).toReal) ∈ realEpigraph f := EReal.le_coe_toReal (ne_of_lt hy)
  have hp := hf hpx hpy ha hb hab
  change f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) at hp
  exact lt_of_le_of_lt hp (EReal.coe_lt_top _)

theorem effectiveDomain_indicator (V : Set E) :
    effectiveDomain (extendedIndicator V) = V := by
  classical
  ext x
  by_cases hx : x ∈ V <;> simp [effectiveDomain, extendedIndicator, hx]

theorem convex_indicator_iff (V : Set E) :
    IsConvexExtended (extendedIndicator V) ↔ Convex ℝ V := by
  constructor
  · intro hf
    simpa only [effectiveDomain_indicator] using convex_effectiveDomain (extendedIndicator V) hf
  · intro hV
    change Convex ℝ (realEpigraph (extendedIndicator V))
    have he : realEpigraph (extendedIndicator V) = V ×ˢ Ici (0 : ℝ) := by
      classical
      ext p
      by_cases hx : p.1 ∈ V <;> simp [realEpigraph, extendedIndicator, hx]
    rw [he]
    exact hV.prod (convex_Ici 0)

theorem realEpigraph_toReal (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) :
    realEpigraph f = {p : E × ℝ | p.1 ∈ effectiveDomain f ∧ (f p.1).toReal ≤ p.2} := by
  ext p
  constructor
  · intro hp
    have ht : f p.1 < ⊤ := lt_of_le_of_lt hp (EReal.coe_lt_top _)
    refine ⟨ht, ?_⟩
    simpa using EReal.toReal_le_toReal hp (hbot p.1) (EReal.coe_ne_top p.2)
  · rintro ⟨hx, hr⟩
    change f p.1 ≤ (p.2 : EReal)
    calc
      f p.1 = ((f p.1).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hbot p.1)).symm
      _ ≤ (p.2 : EReal) := EReal.coe_le_coe hr

theorem convexExtended_iff_toReal (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) :
    IsConvexExtended f ↔ ConvexOn ℝ (effectiveDomain f) (fun x => (f x).toReal) := by
  unfold IsConvexExtended
  rw [realEpigraph_toReal f hbot]
  exact (convexOn_iff_convex_epigraph (𝕜 := ℝ)
    (s := effectiveDomain f) (f := fun x => (f x).toReal)).symm

theorem theorem_2_4 (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hdom : Convex ℝ (effectiveDomain f)) :
    IsConvexExtended f ↔ ∀ x ∈ effectiveDomain f, ∀ y ∈ effectiveDomain f,
      ∀ θ : ℝ, 0 < θ → θ < 1 →
        f (θ • x + (1 - θ) • y) ≤ (θ : EReal) * f x + ((1 - θ : ℝ) : EReal) * f y := by
  have hfinite (x : E) (hx : x ∈ effectiveDomain f) (y : E) (hy : y ∈ effectiveDomain f)
      (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
      (f (θ • x + (1 - θ) • y) ≤ (θ : EReal) * f x + ((1 - θ : ℝ) : EReal) * f y) ↔
      (f (θ • x + (1 - θ) • y)).toReal ≤ θ * (f x).toReal + (1 - θ) * (f y).toReal := by
    have hz := hdom hx hy hθ.le (sub_nonneg.mpr hθ1.le) (by ring)
    rw [← EReal.coe_toReal (ne_of_lt hz) (hbot _),
      ← EReal.coe_toReal (ne_of_lt hx) (hbot _),
      ← EReal.coe_toReal (ne_of_lt hy) (hbot _),
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simp
  rw [convexExtended_iff_toReal f hbot, convexOn_iff_forall_pos]
  constructor
  · rintro ⟨hd, hf⟩ x hx y hy θ hθ hθ1
    apply (hfinite x hx y hy θ hθ hθ1).mpr
    simpa only [smul_eq_mul] using hf hx hy hθ (sub_pos.mpr hθ1) (by ring)
  · intro hf
    refine ⟨hdom, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst b
    have ha1 : a < 1 := by linarith
    simpa only [smul_eq_mul] using (hfinite x hx y hy a ha ha1).mp (hf x hx y hy a ha ha1)

theorem convex_add_indicator (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hf : IsConvexExtended f) (V : Set E) (hV : Convex ℝ V) :
    IsConvexExtended (fun x => f x + extendedIndicator V x) := by
  have he : realEpigraph (fun x => f x + extendedIndicator V x) =
      realEpigraph f ∩ (V ×ˢ (Set.univ : Set ℝ)) := by
    classical
    ext p
    by_cases hx : p.1 ∈ V
    · simp [realEpigraph, extendedIndicator, hx]
    · simp [realEpigraph, extendedIndicator, hx, EReal.add_top_of_ne_bot (hbot p.1)]
  change Convex ℝ (realEpigraph (fun x => f x + extendedIndicator V x))
  rw [he]
  exact (show Convex ℝ (realEpigraph f) from hf).inter (hV.prod convex_univ)

end BanditRL.OnlineConvex
