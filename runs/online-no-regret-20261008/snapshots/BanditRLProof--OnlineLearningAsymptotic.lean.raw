import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningRegret

open Filter

namespace BanditRL.OnlineLearning

/-- The source guessing strategy is no-regret against every fixed interval comparator. -/
theorem meanPredict_noRegret (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2) (meanPredict y) := by
  apply noRegret_of_vanishing_bound _ _ _ (fun _ T => (4 + 4 * Real.log T) / T)
  · intro u hu
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
    have hmain := theorem_1_3 y T hT (fun t ht => hy t)
    have hmin := empiricalMean_minimizes y T hT u
    unfold comparatorRegret
    linarith
  · intro u hu
    have h0 : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hc : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hh := ((h0.comp hc).const_mul 4).add ((h1.comp hc).const_mul 4)
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    ext T
    dsimp [Function.comp_def]
    ring

end BanditRL.OnlineLearning
