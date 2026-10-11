import BanditRLProof.OnlineCumulativeOptimisticStability

noncomputable section
open Set Finset
namespace BanditRL.OnlineConvex

theorem cumulative_optimistic_stability_dual_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hV : Convex ℝ V)
    (psi hint : E → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (lam : ℝ)
    (hbot : ∀ i < n + 1, ∀ x, loss i x ≠ ⊥)
    (hdom : ∀ i < n + 1, V ⊆ effectiveDomain (loss i))
    (hlam : 0 < lam)
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
      ‖g‖ ^ 2 / (2 * lam) := by
  have hlamNonneg : 0 ≤ lam := le_of_lt hlam
  have hb := cumulative_optimistic_stability V hV psi hint loss n lam
    hbot hdom hlamNonneg hstrong p hp hprediction g hdifference q hq
  have ho : g (p - q) ≤ ‖g‖ * ‖p - q‖ := by
    exact le_trans (le_abs_self _) (by
      simpa only [Real.norm_eq_abs] using g.le_opNorm (p - q))
  refine hb.trans ?_
  have hden : 0 < 2 * lam := by positivity
  apply (le_div_iff₀ hden).2
  have hm := mul_le_mul_of_nonneg_right ho (le_of_lt hden)
  nlinarith [sq_nonneg (lam * ‖p - q‖ - ‖g‖)]


end BanditRL.OnlineConvex
