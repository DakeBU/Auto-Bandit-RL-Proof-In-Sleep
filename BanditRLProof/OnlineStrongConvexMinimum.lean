import BanditRLProof.OnlineClosedProper
import Mathlib.Analysis.Convex.Strong

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem stronglyConvex_minimum_growth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hV : Convex ℝ V)
    (hdom : V ⊆ effectiveDomain f) (hlam : 0 ≤ lam)
    (hstrong : ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    (p : E) (hp : p ∈ V) (hmin : IsMinOn f V p)
    (q : E) (hq : q ∈ V) :
    (f p).toReal + (lam / 2) * ‖q - p‖ ^ 2 ≤ (f q).toReal := by
  have hfinite (x : E) (hx : x ∈ V) : ((f x).toReal : EReal) = f x :=
    EReal.coe_toReal (ne_of_lt (hdom hx)) (hf.1 x)
  have hbase : (f p).toReal ≤ (f q).toReal := by
    exact EReal.toReal_le_toReal (hmin hq) (hf.1 p) (ne_of_lt (hdom hq))
  let c : ℝ := (lam / 2) * ‖q - p‖ ^ 2
  have hc : 0 ≤ c := mul_nonneg (div_nonneg hlam (by norm_num)) (sq_nonneg _)
  change (f p).toReal + c ≤ (f q).toReal
  by_contra hfail
  have hgap : (f q).toReal - (f p).toReal < c := by linarith
  have hcpos : 0 < c := by linarith
  let a : ℝ := ((f q).toReal - (f p).toReal + c) / (2 * c)
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one (by positivity : 0 < 2 * c)).2
    linarith
  have hac : 2 * c * a = (f q).toReal - (f p).toReal + c := by
    dsimp [a]
    field_simp
  have hseg : a • p + (1 - a) • q ∈ V :=
    hV hp hq ha.le (by linarith) (by ring)
  have hineq := (hmin hseg).trans (hstrong p hp q hq a ha ha1)
  rw [← hfinite p hp, ← hfinite q hq, norm_sub_rev p q] at hineq
  have hr : (f p).toReal ≤ a * (f p).toReal + (1 - a) * (f q).toReal -
      ((lam / 2) * a * (1 - a) * ‖q - p‖ ^ 2) := by
    exact_mod_cast hineq
  have hmul : 0 < (1 - a) * (c * a - ((f q).toReal - (f p).toReal)) :=
    mul_pos (by linarith) (by nlinarith [hac])
  dsimp [c] at hmul
  nlinarith


end BanditRL.OnlineConvex
