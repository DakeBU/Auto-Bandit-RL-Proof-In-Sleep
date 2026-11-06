import BanditRLProof.OnlineGammaSimplexCurvature

open Set Finset
namespace BanditRL.OnlineGamma

theorem continuousOn_and_convexOn_sum_simplexLogFactor :
  ∀ (n : ℕ) (_hn : 1 ≤ n) (T : ℝ) (_hT : 1 ≤ T),
    let G : (Fin n → ℝ) → ℝ := fun x => ∑ i, simplexLogFactor (x i)
    ContinuousOn G (nonnegativeMassSimplex n T) ∧
      ConvexOn ℝ (nonnegativeMassSimplex n T) G := by
  intro n _hn T _hT
  dsimp only
  constructor
  · apply continuousOn_finset_sum
    intro i _
    exact continuousOn_simplexLogFactor_and_zero.1.comp
      (continuous_apply i).continuousOn (fun x hx => hx.1 i)
  · constructor
    · intro x hx y hy a b ha hb hab
      constructor
      · intro i
        exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
      · change (∑ i, (a * x i + b * y i)) = T
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2,
          ← add_mul, hab, one_mul]
    · intro x hx y hy a b ha hb hab
      change (∑ i, simplexLogFactor (a * x i + b * y i)) ≤
        a * (∑ i, simplexLogFactor (x i)) + b * (∑ i, simplexLogFactor (y i))
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ =>
        simplexLogFactor_convexOn.2 (hx.1 i) (hy.1 i) ha hb hab

end BanditRL.OnlineGamma
