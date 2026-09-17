import BanditRLProof.Algorithms.HeavyTailExpectedCount
import BanditRLProof.Algorithms.ETCRealInfinitePiTail
import BanditRLProof.RealMeanRegretPullCount

/-!
Conservative robust-UCB expected pseudo-regret endpoint. This is the separately
documented repair/adaptation, not the unchanged printed BCL constant theorem.
The policy and measure are fixed across horizons. Zero-gap arms contribute zero.
-/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory
variable {K : ℕ}

theorem integrable_id_of_raw_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 ≤ ε) (hm : Integrable (fun x : ℝ => |x|^(1+ε)) μ) :
    Integrable (fun x : ℝ => x) μ := by
  apply ((integrable_const (1 : ℝ)).add hm).mono' measurable_id.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change |x| ≤ 1 + |x|^(1+ε)
    by_cases hx : |x| ≤ 1
    · have hp := Real.rpow_nonneg (abs_nonneg x) (1+ε)
      linarith
    · have hp := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) (show (1 : ℝ) ≤ 1+ε by linarith)
      rw [Real.rpow_one] at hp
      linarith

theorem robust_expected_regret (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (ε u : ℝ) (T : ℕ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫ stream, realMeanRegret (realKernelMean ν) (robustAction hK ε u stream) T
      ∂UCB.armStreamMeasure ν) ≤
    ∑ arm : Fin K, realMeanGap (realKernelMean ν) arm *
      (gapThreshold ε u (realMeanGap (realKernelMean ν) arm) T + 2) := by
  have hX : ∀ a, Integrable (fun x : ℝ => x) (ν a) := fun a =>
    integrable_id_of_raw_moment (ν a) ε hε0.le (hm a)
  rw [integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount
    (UCB.armStreamMeasure ν) (realKernelMean ν) (robustAction hK ε u) T
    (fun arm => robust_integrable_count hK ν arm ε u T)]
  apply Finset.sum_le_sum
  intro arm _
  have he : realMeanGap (realKernelMean ν) arm =
      realKernelMean ν (ETC.realKernelBestArm hK ν) - realKernelMean ν arm := by
    rw [realMeanGap, ETC.ciSup_realKernelMean_eq_realKernelBestArm hK ν]
  have hg : 0 ≤ realMeanGap (realKernelMean ν) arm := by
    rw [he]
    exact sub_nonneg.mpr (ETC.realKernelMean_le_realKernelBestArm hK ν arm)
  rcases eq_or_lt_of_le hg with hz | hp
  · rw [← hz]; simp
  · apply mul_le_mul_of_nonneg_left _ hg
    rw [he]
    exact robust_integral_count_le hK ν (ETC.realKernelBestArm hK ν) arm ε u T hε0 hε hu0
      (by simpa only [he, realKernelMean] using hp) hX hm hu

theorem robust_regret_integrable (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (ε u : ℝ) (T : ℕ) :
    Integrable (fun stream => realMeanRegret (realKernelMean ν) (robustAction hK ε u stream) T)
      (UCB.armStreamMeasure ν) :=
  integrable_realMeanRegret_of_integrable_pullCount (UCB.armStreamMeasure ν)
    (realKernelMean ν) (robustAction hK ε u) T (fun arm => robust_integrable_count hK ν arm ε u T)

end BanditRLProof.HeavyTail
