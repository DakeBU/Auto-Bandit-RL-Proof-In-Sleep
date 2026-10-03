import BanditRLProof.HeavyTailClippedScheduled
import BanditRLProof.HeavyTailArmLaw

/-! Raw-moment confidence under a pathwise corruption budget on the consumed
prefix. The count and corruption may depend on the entire outcome. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem integrable_of_raw_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (ε : ℝ)
    (hXm : Measurable X) (hε : 0 ≤ ε)
    (hm : Integrable (fun ω => |X ω|^(1+ε)) μ) : Integrable X μ := by
  apply ((integrable_const (1 : ℝ)).add hm).mono' hXm.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change |X ω| ≤ 1 + |X ω|^(1+ε)
    by_cases hx : |X ω| ≤ 1
    · have hp := Real.rpow_nonneg (abs_nonneg (X ω)) (1+ε)
      linarith
    · have hp := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx)
        (show (1 : ℝ) ≤ 1+ε by linarith)
      rw [Real.rpow_one] at hp
      linarith

/-- No clean-confidence or fluctuation premise: these are produced from the
independent raw-moment stream. Only the actually consumed prefix is budgeted. -/
theorem adaptive_corrupted_clipped_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X c : ℕ → Ω → ℝ)
    (count : Ω → ℕ) (ε u mean C : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u)
    (hC : ∀ ω, (∑ s ∈ Finset.range (count ω), |c s ω|) ≤ C) :
    μ.real {ω | 0 < count ω ∧ count ω ≤ t ∧
      confidenceRadius ε u t (count ω) + C / count ω ≤
        |prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω + c s ω))
          (count ω) - mean|} ≤ t * (2 * Real.exp (-confidenceLog t)) := by
  have htail := scheduled_adaptive_clipped_mean_tail μ X count ε u mean t
    hXm hi hε0 hε hu0 (fun i => integrable_of_raw_moment μ (X i) ε (hXm i) hε0 (hm i))
    hmean hm hu
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans htail
  intro ω hω
  refine ⟨hω.1, hω.2.1, ?_⟩
  have hp := clipped_prefix_corruption_le (fun s => X s ω) (fun s => c s ω)
    (sampleThreshold ε u t) (count ω) C (hC ω)
  have ht := abs_sub_le
    (prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω + c s ω)) (count ω))
    (prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω)) (count ω)) mean
  change confidenceRadius ε u t (count ω) ≤
    |prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω)) (count ω) - mean|
  linarith [hω.2.2]

/-- Confidence for the actual clipped observations along an arbitrary action
trace, including a policy driven by corrupted observations. This compares clean
and corrupted rewards along that same trace, not two different policies. -/
theorem observed_corrupted_clipped_mean_tail {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (action : Ω → ActionTrace (Fin K)) (stream corruption : Ω → UCB.ArmRewardStream K)
    (arm : Fin K) (ε u mean C : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (fun ω => stream ω i arm))
    (hi : iIndepFun (fun i ω => stream ω i arm) μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hmean : ∀ i, (∫ ω, stream ω i arm ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |stream ω i arm|^(1+ε)) μ)
    (hu : ∀ i, (∫ ω, |stream ω i arm|^(1+ε) ∂μ) ≤ u)
    (hC : ∀ ω, (∑ s ∈ Finset.range (pullCount (action ω) arm t),
      |corruption ω s arm|) ≤ C) :
    μ.real {ω | 0 < pullCount (action ω) arm t ∧ pullCount (action ω) arm t ≤ t ∧
      confidenceRadius ε u t (pullCount (action ω) arm t) +
        C / pullCount (action ω) arm t ≤
      |sumRewards (action ω)
        (fun s => clip (sampleThreshold ε u t (pullCount (action ω) (action ω s) s))
          (UCB.rewardFromArmStream action
            (fun ω j a => stream ω j a + corruption ω j a) ω s)) arm t /
        pullCount (action ω) arm t - mean|} ≤
      t * (2 * Real.exp (-confidenceLog t)) := by
  have htail := adaptive_corrupted_clipped_mean_tail μ
    (fun i ω => stream ω i arm) (fun i ω => corruption ω i arm)
    (fun ω => pullCount (action ω) arm t) ε u mean C t
    hXm hi hε0 hε hu0 hmean hm hu hC
  simpa only [prefixMean,
    clipped_observed_prefix action stream corruption (fun j _ => sampleThreshold ε u t j)]
    using htail

/-- Stationary arm laws supply the coordinate independence and moments for the
reserved transfer endpoint. No confidence bound is supplied by the caller. -/
theorem arm_corrupted_clipped_mean_tail {K : ℕ}
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (count : UCB.ArmRewardStream K → ℕ)
    (c : ℕ → UCB.ArmRewardStream K → ℝ) (ε u C : ℝ) (t : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u)
    (hC : ∀ stream, (∑ s ∈ Finset.range (count stream), |c s stream|) ≤ C) :
    (UCB.armStreamMeasure ν).real {stream | 0 < count stream ∧ count stream ≤ t ∧
      confidenceRadius ε u t (count stream) + C / count stream ≤
      |prefixMean (fun s => clip (sampleThreshold ε u t s) (stream s arm + c s stream))
        (count stream) - ∫ x, x ∂ν arm|} ≤ t * (2 * Real.exp (-confidenceLog t)) := by
  apply adaptive_corrupted_clipped_mean_tail (UCB.armStreamMeasure ν)
    (fun s stream => stream s arm) c count ε u _ C t
    (fun i => (measurable_pi_apply arm).comp (measurable_pi_apply i))
  · simpa only [sub_zero] using UCB.iIndepFun_armStreamMeasure_coord_sub ν arm 0
  · exact hε0
  · exact hε
  · exact hu0
  · exact fun i => arm_coordinate_integral ν arm i _ measurable_id
  · exact fun i => arm_coordinate_integrable ν arm i _ hm
  · intro i
    rw [arm_coordinate_integral ν arm i (fun x : ℝ => |x|^(1+ε)) (by fun_prop)]
    exact hu
  · exact hC

end BanditRLProof.HeavyTail
