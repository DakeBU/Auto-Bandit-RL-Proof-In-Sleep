import BanditRLProof.OnlineStrongConvexMinimum
import Mathlib.Analysis.Normed.Operator.Basic

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem stronglyConvex_support_growth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hV : Convex ℝ V)
    (hdom : V ⊆ effectiveDomain f) (hlam : 0 ≤ lam)
    (hstrong : ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    (p : E) (hp : p ∈ V) (g : E →L[ℝ] ℝ)
    (hsupport : ∀ z ∈ V, f p + (g (z - p) : EReal) ≤ f z)
    (q : E) (hq : q ∈ V) :
    (f p).toReal + g (q - p) + (lam / 2) * ‖q - p‖ ^ 2 ≤ (f q).toReal := by
  have hfinite (x : E) (hx : x ∈ V) : ((f x).toReal : EReal) = f x :=
    EReal.coe_toReal (ne_of_lt (hdom hx)) (hf.1 x)
  let F : E → EReal := fun x => f x - (g (x - p) : EReal)
  have hFfinite (x : E) (hx : x ∈ V) :
      F x = ((f x).toReal - g (x - p) : ℝ) := by
    dsimp [F]
    rw [← hfinite x hx]
    rfl
  have hFproper : SourceProper F := by
    refine ⟨?_, ⟨p, (f p).toReal - g (p - p), hFfinite p hp⟩⟩
    intro x
    dsimp [F]
    rw [sub_eq_add_neg]
    exact EReal.add_ne_bot_iff.mpr ⟨hf.1 x, by
      rw [← EReal.coe_neg]
      exact EReal.coe_ne_bot _⟩
  have hFdom : V ⊆ effectiveDomain F := by
    intro x hx
    change F x < ⊤
    rw [hFfinite x hx]
    exact EReal.coe_lt_top _
  have hFstrong : ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      F (a • x + (1 - a) • y) ≤
        (a : EReal) * F x + ((1 - a : ℝ) : EReal) * F y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz : a • x + (1 - a) • y ∈ V :=
      hV hx hy ha.le (by linarith) (by ring)
    have hs := hstrong x hx y hy a ha ha1
    rw [← hfinite _ hz, ← hfinite x hx, ← hfinite y hy] at hs
    have hr : (f (a • x + (1 - a) • y)).toReal ≤
        a * (f x).toReal + (1 - a) * (f y).toReal -
          (lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 := by
      exact_mod_cast hs
    have hg : g (a • x + (1 - a) • y - p) =
        a * g (x - p) + (1 - a) * g (y - p) := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul]
      ring
    rw [hFfinite _ hz, hFfinite x hx, hFfinite y hy]
    have ht : (f (a • x + (1 - a) • y)).toReal -
        g (a • x + (1 - a) • y - p) ≤
        a * ((f x).toReal - g (x - p)) +
          (1 - a) * ((f y).toReal - g (y - p)) -
          (lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 := by
      rw [hg]
      nlinarith [hr]
    exact_mod_cast ht
  have hFmin : IsMinOn F V p := by
    intro z hz
    change F p ≤ F z
    have hs := hsupport z hz
    rw [← hfinite p hp, ← hfinite z hz] at hs
    have hr : (f p).toReal + g (z - p) ≤ (f z).toReal := by
      exact_mod_cast hs
    rw [hFfinite p hp, hFfinite z hz]
    have ht : (f p).toReal - g (p - p) ≤ (f z).toReal - g (z - p) := by
      simp only [sub_self, map_zero, sub_zero]
      linarith
    exact_mod_cast ht
  have hgrowth := stronglyConvex_minimum_growth F V lam hFproper hV hFdom
    hlam hFstrong p hp hFmin q hq
  rw [hFfinite p hp, hFfinite q hq] at hgrowth
  simp only [EReal.toReal_coe, sub_self, map_zero, sub_zero] at hgrowth
  linarith


end BanditRL.OnlineConvex

run_cmd do
  let env ← Lean.getEnv
  let some ci := env.find? `BanditRL.OnlineConvex.stronglyConvex_support_growth
    | throwError "missing theorem"
  let value ← match ci with
    | .thmInfo i => pure i.value
    | _ => throwError "not theorem"
  Lean.logInfo ("ACTUAL_EXPR_JSON=" ++ (Lean.Json.mkObj [
    ("TYPE_REPR", Lean.Json.str (reprStr ci.type)),
    ("VALUE_REPR", Lean.Json.str (reprStr value))]).compress)
