import BanditRLProof.Algorithms.HeavyTailSourceExpectedCount
import BanditRLProof.Algorithms.HeavyTailRegret

/-! Complete corrected expected-regret bound for the unchanged source policy.
The rejected printed coefficient remains a separate finite-counterexample obligation. -/
namespace BanditRLProof.HeavyTail.SourcePolicy
open MeasureTheory ProbabilityTheory
variable {K : ℕ}

/-- Raw moments produce the entire causal algorithm-to-expected-pseudo-regret chain. -/
theorem robust_expected_regret (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (ε u : ℝ) (T : ℕ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫ stream, realMeanRegret (realKernelMean ν) (robustAction hK ε u stream) T
      ∂UCB.armStreamMeasure ν) ≤
    ∑ arm ∈ Finset.univ.filter (fun arm : Fin K => 0 < realMeanGap (realKernelMean ν) arm),
      realMeanGap (realKernelMean ν) arm *
        (gapBudget ε u (realMeanGap (realKernelMean ν) arm) T + 5) := by
  have hX : ∀ a, Integrable (fun x : ℝ => x) (ν a) := fun a =>
    integrable_id_of_raw_moment (ν a) ε hε0.le (hm a)
  rw [integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount
    (UCB.armStreamMeasure ν) (realKernelMean ν) (robustAction hK ε u) T
    (fun arm => robust_integrable_count hK ν arm ε u T), Finset.sum_filter]
  apply Finset.sum_le_sum
  intro arm _
  have he : realMeanGap (realKernelMean ν) arm =
      realKernelMean ν (ETC.realKernelBestArm hK ν) - realKernelMean ν arm := by
    rw [realMeanGap, ETC.ciSup_realKernelMean_eq_realKernelBestArm hK ν]
  have hg : 0 ≤ realMeanGap (realKernelMean ν) arm := by
    rw [he]
    exact sub_nonneg.mpr (ETC.realKernelMean_le_realKernelBestArm hK ν arm)
  by_cases hp : 0 < realMeanGap (realKernelMean ν) arm
  · rw [if_pos hp]
    apply mul_le_mul_of_nonneg_left _ hg
    rw [he]
    exact robust_integral_count_le_budget hK ν (ETC.realKernelBestArm hK ν) arm ε u T hε0 hε hu0
      (by simpa only [he, realKernelMean] using hp) hX hm hu
  · rw [if_neg hp]
    have hz : realMeanGap (realKernelMean ν) arm = 0 := le_antisymm (not_lt.mp hp) hg
    simp [hz]

theorem robust_regret_integrable (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (ε u : ℝ) (T : ℕ) :
    Integrable (fun stream => realMeanRegret (realKernelMean ν) (robustAction hK ε u stream) T)
      (UCB.armStreamMeasure ν) :=
  integrable_realMeanRegret_of_integrable_pullCount (UCB.armStreamMeasure ν)
    (realKernelMean ν) (robustAction hK ε u) T (fun arm => robust_integrable_count hK ν arm ε u T)

end BanditRLProof.HeavyTail.SourcePolicy
