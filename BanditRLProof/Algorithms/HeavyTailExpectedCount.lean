import BanditRLProof.Algorithms.HeavyTailAdaptive
import BanditRLProof.HeavyTailTailSum

/-! Expected pull counts for the actual robust policy under raw-moment reward laws. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {K : ℕ}

theorem lintegral_pullCount_threshold {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω → ActionTrace (Fin K))
    (ha : ∀ t, Measurable (fun ω => a ω t)) (arm : Fin K) (T B : ℕ) :
    (∫⁻ ω, (pullCount (a ω) arm T : ℝ≥0∞) ∂μ) ≤
      B + ∑ t ∈ Finset.range T, μ {ω | a ω t = arm ∧ B ≤ pullCount (a ω) arm t} := by
  let C := fun ω => ∑ t ∈ Finset.range T,
    if a ω t = arm ∧ B ≤ pullCount (a ω) arm t then (1 : ℝ≥0∞) else 0
  calc
    _ ≤ ∫⁻ ω, (B : ℝ≥0∞) + C ω ∂μ := lintegral_mono fun ω =>
      UCB.natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum (a ω) arm T B
    _ = (B : ℝ≥0∞) + ∫⁻ ω, C ω ∂μ := by rw [lintegral_add_left measurable_const]; simp
    _ = _ := by
      dsimp [C]
      rw [UCB.lintegral_selectedLargePullCount_indicator_sum_eq_sum_measure μ a ha arm T B]

theorem robust_lintegral_count_le (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (T : ℕ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hgap : 0 < (∫ x, x ∂ν best) - ∫ x, x ∂ν arm)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫⁻ stream, (pullCount (robustAction hK ε u stream) arm T : ℝ≥0∞) ∂UCB.armStreamMeasure ν) ≤
      gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T + 2 := by
  apply (lintegral_pullCount_threshold (UCB.armStreamMeasure ν) (robustAction hK ε u)
    (measurable_robustAction hK ε u) arm T
    (gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T)).trans
  apply add_le_add (le_refl _)
  calc
    _ ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal (4*t*Real.exp (-confidenceLog t)) := by
      apply Finset.sum_le_sum
      intro t ht
      have h := ENNReal.ofReal_le_ofReal (robust_large_count_tail hK ν best arm ε u T t
        (Finset.mem_range.mp ht).le hε0 hε hu0 hgap hX hm hu)
      rwa [ofReal_measureReal (measure_ne_top _ _)] at h
    _ = ENNReal.ofReal (∑ t ∈ Finset.range T, 4*t*Real.exp (-confidenceLog t)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)).symm
    _ ≤ 2 := by exact_mod_cast ENNReal.ofReal_le_ofReal (scheduled_tail_sum_le_two T)

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
    (ε u : ℝ) (T : ℕ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hgap : 0 < (∫ x, x ∂ν best) - ∫ x, x ∂ν arm)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫ stream, (pullCount (robustAction hK ε u stream) arm T : ℝ) ∂UCB.armStreamMeasure ν) ≤
      gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T + 2 := by
  have h := robust_lintegral_count_le hK ν best arm ε u T hε0 hε hu0 hgap hX hm hu
  have he := ofReal_integral_eq_lintegral_ofReal (robust_integrable_count hK ν arm ε u T)
    (ae_of_all _ (fun stream => Nat.cast_nonneg (pullCount (robustAction hK ε u stream) arm T)))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he] at h
  have hr := (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp h
  simpa using hr

end BanditRLProof.HeavyTail
