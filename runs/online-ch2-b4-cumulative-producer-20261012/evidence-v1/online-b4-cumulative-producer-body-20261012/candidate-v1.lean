import BanditRLProof.OnlinePrescientBregmanSource
import Mathlib.Analysis.Convex.Strong
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Set Finset
namespace BanditRL.OnlineConvex

theorem cumulative_regularizer_source_strongConvex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hV : V.Nonempty)
    (psi : E → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hpsi : StrongConvexOn V lam psi)
    (hbot : ∀ i < n, ∀ x, loss i x ≠ ⊥)
    (hdom : ∀ i < n, V ⊆ effectiveDomain (loss i))
    (hloss : ∀ i < n, ConvexOn ℝ V (fun x => (loss i x).toReal)) :
    let F : E → EReal := fun x =>
      (psi x : EReal) + ∑ i ∈ range n, loss i x + extendedIndicator V x
    SourceProper F ∧ effectiveDomain F = V ∧
      (∀ x ∈ V, F x = ((psi x + ∑ i ∈ range n, (loss i x).toReal : ℝ) : EReal)) ∧
      (∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
        F (a • x + (1 - a) • y) ≤
          (a : EReal) * F x + ((1 - a : ℝ) : EReal) * F y -
            (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
  classical
  let F : E → EReal := fun x =>
    (psi x : EReal) + ∑ i ∈ range n, loss i x + extendedIndicator V x
  change SourceProper F ∧ effectiveDomain F = V ∧ _ ∧ _
  have hfinite (i : ℕ) (hi : i < n) (x : E) (hx : x ∈ V) :
      ((loss i x).toReal : EReal) = loss i x :=
    EReal.coe_toReal (ne_of_lt (hdom i hi hx)) (hbot i hi x)
  have hsumBot (m : ℕ) (hm : m ≤ n) (x : E) :
      (∑ i ∈ range m, loss i x) ≠ ⊥ := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      exact EReal.add_ne_bot_iff.mpr
        ⟨ih (Nat.le_trans (Nat.le_succ m) hm), hbot m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm) x⟩
  have hsumFinite (m : ℕ) (hm : m ≤ n) (x : E) (hx : x ∈ V) :
      (∑ i ∈ range m, loss i x) = ((∑ i ∈ range m, (loss i x).toReal : ℝ) : EReal) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, sum_range_succ, ih (Nat.le_trans (Nat.le_succ m) hm),
        ← hfinite m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm) x hx, EReal.coe_add]
  have hvalue (x : E) (hx : x ∈ V) :
      F x = ((psi x + ∑ i ∈ range n, (loss i x).toReal : ℝ) : EReal) := by
    dsimp [F]
    rw [hsumFinite n le_rfl x hx]
    simp only [extendedIndicator, if_pos hx, add_zero, EReal.coe_add]
  have hout (x : E) (hx : x ∉ V) : F x = ⊤ := by
    dsimp [F]
    rw [show extendedIndicator V x = ⊤ by simp [extendedIndicator, hx]]
    exact EReal.add_top_of_ne_bot
      (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hsumBot n le_rfl x⟩)
  have hFbot (x : E) : F x ≠ ⊥ := by
    by_cases hx : x ∈ V
    · rw [hvalue x hx]
      exact EReal.coe_ne_bot _
    · rw [hout x hx]
      exact top_ne_bot
  have hFdom : effectiveDomain F = V := by
    ext x
    by_cases hx : x ∈ V
    · simp only [effectiveDomain, mem_setOf_eq, hvalue x hx, EReal.coe_lt_top, hx]
    · simp only [effectiveDomain, mem_setOf_eq, hout x hx, lt_self_iff_false, hx]
  have hproper : SourceProper F :=
    sourceProper_of_domain F V hV hFbot (by rw [hFdom])
  refine ⟨hproper, hFdom, hvalue, ?_⟩
  intro x hx y hy a ha ha1
  have hz : a • x + (1 - a) • y ∈ V :=
    hpsi.1 hx hy ha.le (by linarith) (by ring)
  have hp := hpsi.2 hx hy ha.le (show 0 ≤ 1 - a by linarith) (show a + (1 - a) = 1 by ring)
  have hs : (∑ i ∈ range n, (loss i (a • x + (1 - a) • y)).toReal) ≤
      a * (∑ i ∈ range n, (loss i x).toReal) +
      (1 - a) * (∑ i ∈ range n, (loss i y).toReal) := by
    have h := Finset.sum_le_sum (s := range n) (fun i hi =>
      (hloss i (mem_range.mp hi)).2 hx hy ha.le (show 0 ≤ 1 - a by linarith)
        (show a + (1 - a) = 1 by ring))
    simpa only [smul_eq_mul, sum_add_distrib, mul_sum] using h
  have hr : psi (a • x + (1 - a) • y) +
      (∑ i ∈ range n, (loss i (a • x + (1 - a) • y)).toReal) ≤
      a * (psi x + ∑ i ∈ range n, (loss i x).toReal) +
      (1 - a) * (psi y + ∑ i ∈ range n, (loss i y).toReal) -
      (lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 := by
    change psi (a • x + (1 - a) • y) ≤
      a * psi x + (1 - a) * psi y - a * (1 - a) * (lam / 2 * ‖x - y‖ ^ 2) at hp
    nlinarith [hp, hs]
  rw [hvalue _ hz, hvalue x hx, hvalue y hy]
  exact_mod_cast hr

end BanditRL.OnlineConvex
