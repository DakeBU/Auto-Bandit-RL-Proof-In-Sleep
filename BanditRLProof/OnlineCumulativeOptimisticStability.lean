import BanditRLProof.OnlineStrongConvexSupport
import BanditRLProof.OnlinePrescientBregmanSource
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Set Finset
namespace BanditRL.OnlineConvex

theorem cumulative_optimistic_stability {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hV : Convex ℝ V)
    (psi hint : E → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (lam : ℝ)
    (hbot : ∀ i < n + 1, ∀ x, loss i x ≠ ⊥)
    (hdom : ∀ i < n + 1, V ⊆ effectiveDomain (loss i))
    (hlam : 0 ≤ lam)
    (hstrong : let G : E → EReal := fun x =>
        (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
      ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
        G (a • x + (1 - a) • y) ≤
          (a : EReal) * G x + ((1 - a : ℝ) : EReal) * G y -
            (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    (p : E) (hp : p ∈ V)
    (hprediction : IsMinOn (fun x =>
      (psi x : EReal) + ∑ i ∈ range n, loss i x + (hint x : EReal)) V p)
    (g : E →L[ℝ] ℝ)
    (hdifference : ∀ z ∈ V,
      (loss n p).toReal - hint p + g (z - p) ≤ (loss n z).toReal - hint z)
    (q : E) (hq : q ∈ V) :
    let G : E → EReal := fun x =>
      (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
    (G p).toReal - (G q).toReal ≤
      g (p - q) - (lam / 2) * ‖p - q‖ ^ 2 := by
  classical
  let G : E → EReal := fun x =>
    (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
  change (G p).toReal - (G q).toReal ≤ g (p - q) - (lam / 2) * ‖p - q‖ ^ 2
  have hfinite (i : ℕ) (hi : i < n + 1) (x : E) (hx : x ∈ V) :
      ((loss i x).toReal : EReal) = loss i x :=
    EReal.coe_toReal (ne_of_lt (hdom i hi hx)) (hbot i hi x)
  have hsumBot (m : ℕ) (hm : m ≤ n + 1) (x : E) :
      (∑ i ∈ range m, loss i x) ≠ ⊥ := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      exact EReal.add_ne_bot_iff.mpr
        ⟨ih (Nat.le_trans (Nat.le_succ m) hm),
          hbot m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm) x⟩
  have hsumFinite (m : ℕ) (hm : m ≤ n + 1) (x : E) (hx : x ∈ V) :
      (∑ i ∈ range m, loss i x) = ((∑ i ∈ range m, (loss i x).toReal : ℝ) : EReal) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, sum_range_succ, ih (Nat.le_trans (Nat.le_succ m) hm),
        ← hfinite m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm) x hx, EReal.coe_add]
      simp only [EReal.toReal_coe]
  have hvalue (x : E) (hx : x ∈ V) :
      G x = ((psi x + ∑ i ∈ range (n + 1), (loss i x).toReal : ℝ) : EReal) := by
    dsimp [G]
    rw [hsumFinite (n + 1) le_rfl x hx]
    simp only [extendedIndicator, if_pos hx, add_zero]
  have hout (x : E) (hx : x ∉ V) : G x = ⊤ := by
    dsimp [G]
    rw [show extendedIndicator V x = ⊤ by simp [extendedIndicator, hx]]
    exact EReal.add_top_of_ne_bot
      (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hsumBot (n + 1) le_rfl x⟩)
  have hGbot (x : E) : G x ≠ ⊥ := by
    by_cases hx : x ∈ V
    · rw [hvalue x hx]
      exact EReal.coe_ne_bot _
    · rw [hout x hx]
      exact top_ne_bot
  have hGdom : V ⊆ effectiveDomain G := by
    intro x hx
    change G x < ⊤
    rw [hvalue x hx]
    exact EReal.coe_lt_top _
  have hproper : SourceProper G := sourceProper_of_domain G V ⟨p, hp⟩ hGbot hGdom
  have hprior (x : E) (hx : x ∈ V) :
      (psi x : EReal) + ∑ i ∈ range n, loss i x + (hint x : EReal) =
        ((psi x + ∑ i ∈ range n, (loss i x).toReal + hint x : ℝ) : EReal) := by
    rw [hsumFinite n (Nat.le_succ n) x hx]
    simp only [EReal.coe_add]
  have hsupport : ∀ z ∈ V, G p + (g (z - p) : EReal) ≤ G z := by
    intro z hz
    have hm := hprediction hz
    change (psi p : EReal) + ∑ i ∈ range n, loss i p + (hint p : EReal) ≤
      (psi z : EReal) + ∑ i ∈ range n, loss i z + (hint z : EReal) at hm
    rw [hprior p hp, hprior z hz] at hm
    have hmr : psi p + ∑ i ∈ range n, (loss i p).toReal + hint p ≤
        psi z + ∑ i ∈ range n, (loss i z).toReal + hint z := by exact_mod_cast hm
    have hd := hdifference z hz
    rw [hvalue p hp, hvalue z hz, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simp only [sum_range_succ]
    linarith [hmr, hd]
  have hb := stronglyConvex_support_growth G V lam hproper hV hGdom hlam
    hstrong p hp g hsupport q hq
  have hcancel : g (q - p) + g (p - q) = 0 := by
    simp only [map_sub]
    ring
  rw [norm_sub_rev q p] at hb
  linarith


end BanditRL.OnlineConvex
