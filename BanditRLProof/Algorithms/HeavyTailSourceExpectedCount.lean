import BanditRLProof.Algorithms.HeavyTailSourceAdaptive
import BanditRLProof.Algorithms.HeavyTailExpectedCount

/-! Corrected expected counts for the unchanged source policy. The shared
threshold-count integral producer is reused; confidence is derived from raw moments. -/
namespace BanditRLProof.HeavyTail.SourcePolicy
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {K : ℕ}

theorem robust_lintegral_count_le (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hgap : 0 < (∫ x, x ∂ν best) - ∫ x, x ∂ν arm)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫⁻ stream, (pullCount (robustAction hK ε u stream) arm T : ℝ≥0∞) ∂UCB.armStreamMeasure ν) ≤
      gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T + 4 := by
  apply (lintegral_pullCount_threshold (UCB.armStreamMeasure ν) (robustAction hK ε u)
    (measurable_robustAction hK ε u) arm T
    (gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T)).trans
  apply add_le_add (le_refl _)
  calc
    _ ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal (2*t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t)) := by
      apply Finset.sum_le_sum
      intro t ht
      have h := ENNReal.ofReal_le_ofReal (robust_large_count_tail hK ν best arm ε u T t hT
        (Finset.mem_range.mp ht) hε0 hε hu0 hgap hX hm hu)
      rwa [ofReal_measureReal (measure_ne_top _ _)] at h
    _ = ENNReal.ofReal (∑ t ∈ Finset.range T, 2*t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)).symm
    _ ≤ 4 := by
      have hs := mul_le_mul_of_nonneg_left (source_schedule_tail_sum_le_two T)
        (by norm_num : (0 : ℝ) ≤ 2)
      have hsum : (∑ t ∈ Finset.range T, 2*t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t)) ≤ 4 := by
        simpa only [Finset.mul_sum, mul_assoc, show (2 : ℝ)*2 = 4 by norm_num] using hs
      exact_mod_cast ENNReal.ofReal_le_ofReal hsum

theorem robust_integrable_count (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (arm : Fin K) (ε u : ℝ) (T : ℕ) :
    Integrable (fun stream => (pullCount (robustAction hK ε u stream) arm T : ℝ))
      (UCB.armStreamMeasure ν) := by
  apply Integrable.of_bound
    (measurable_natCast_pullCount (robustAction hK ε u) (measurable_robustAction hK ε u) arm T).aestronglyMeasurable
    (T : ℝ)
  exact ae_of_all _ fun stream => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast pullCount_le_time (robustAction hK ε u stream) arm T

theorem robust_integral_count_le (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hgap : 0 < (∫ x, x ∂ν best) - ∫ x, x ∂ν arm)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫ stream, (pullCount (robustAction hK ε u stream) arm T : ℝ) ∂UCB.armStreamMeasure ν) ≤
      gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T + 4 := by
  have h := robust_lintegral_count_le hK ν best arm ε u T hT hε0 hε hu0 hgap hX hm hu
  have he := ofReal_integral_eq_lintegral_ofReal (robust_integrable_count hK ν arm ε u T)
    (ae_of_all _ (fun stream => Nat.cast_nonneg (pullCount (robustAction hK ε u stream) arm T)))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he] at h
  have hr := (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp h
  simpa using hr

/-- All horizons, retaining the additive five without a positive-cutoff assumption at T=0/1. -/
theorem robust_integral_count_le_budget (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (T : ℕ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hgap : 0 < (∫ x, x ∂ν best) - ∫ x, x ∂ν arm)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫ stream, (pullCount (robustAction hK ε u stream) arm T : ℝ) ∂UCB.armStreamMeasure ν) ≤
      gapBudget ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T + 5 := by
  have hA := gapBudget_nonneg ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T hu0 hgap
  by_cases hT : 2 ≤ T
  · have h := robust_integral_count_le hK ν best arm ε u T hT hε0 hε hu0 hgap hX hm hu
    have hc := Nat.ceil_lt_add_one hA
    unfold gapThreshold at h
    linarith
  · have hcount : (∫ stream, (pullCount (robustAction hK ε u stream) arm T : ℝ)
        ∂UCB.armStreamMeasure ν) ≤ T := by
      calc
        _ ≤ ∫ _stream, (T : ℝ) ∂UCB.armStreamMeasure ν := integral_mono
          (robust_integrable_count hK ν arm ε u T) (integrable_const _)
          (fun stream => Nat.cast_le.mpr (pullCount_le_time _ _ _))
        _ = _ := by simp
    have hsmall : (T : ℝ) ≤ 1 := by exact_mod_cast (show T ≤ 1 by omega)
    linarith

end BanditRLProof.HeavyTail.SourcePolicy
