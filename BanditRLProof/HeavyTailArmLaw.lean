import BanditRLProof.HeavyTailScheduledConfidence
import BanditRLProof.Algorithms.UCBArmStreamTail

/-! Stationary raw-moment reward laws supply every fixed-coordinate hypothesis. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory
variable {K : ℕ}

theorem arm_coordinate_integral (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ stream, g (stream i arm) ∂UCB.armStreamMeasure ν) = ∫ x, g x ∂ν arm := by
  rw [← UCB.armStreamMeasure_map_coord ν i arm]
  exact (integral_map_of_stronglyMeasurable
    ((measurable_pi_apply arm).comp (measurable_pi_apply i)) hg.stronglyMeasurable).symm

theorem arm_coordinate_integrable (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (i : ℕ) (g : ℝ → ℝ) (hg : Integrable g (ν arm)) :
    Integrable (fun stream => g (stream i arm)) (UCB.armStreamMeasure ν) := by
  have hp : MeasurePreserving (fun stream : UCB.ArmRewardStream K => stream i arm)
      (UCB.armStreamMeasure ν) (ν arm) :=
    ⟨(measurable_pi_apply arm).comp (measurable_pi_apply i), UCB.armStreamMeasure_map_coord ν i arm⟩
  exact hp.integrable_comp_of_integrable hg

theorem arm_adaptive_mean_tail (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (count : UCB.ArmRewardStream K → ℕ) (ε u : ℝ) (t : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream | 0 < count stream ∧ count stream ≤ t ∧
      confidenceRadius ε u t (count stream) ≤
        |(∑ s ∈ Finset.range (count stream), truncate (sampleThreshold ε u t s) (stream s arm)) /
          count stream - ∫ x, x ∂ν arm|} ≤ t * (2 * Real.exp (-confidenceLog t)) := by
  apply scheduled_adaptive_mean_tail (UCB.armStreamMeasure ν) (fun s stream => stream s arm)
    count ε u (∫ x, x ∂ν arm) t
    (fun i => (measurable_pi_apply arm).comp (measurable_pi_apply i))
  · simpa only [sub_zero] using UCB.iIndepFun_armStreamMeasure_coord_sub ν arm 0
  · exact hε0
  · exact hε
  · exact hu0
  · exact fun i => arm_coordinate_integrable ν arm i _ hX
  · exact fun i => arm_coordinate_integral ν arm i _ measurable_id
  · exact fun i => arm_coordinate_integrable ν arm i _ hm
  · intro i
    rw [arm_coordinate_integral ν arm i (fun x : ℝ => |x|^(1+ε)) (by fun_prop)]
    exact hu

end BanditRLProof.HeavyTail
