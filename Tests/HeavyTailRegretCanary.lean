import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof BanditRLProof.HeavyTail
open scoped ENNReal

namespace HeavyTailRegretCanary

-- Each arm is genuinely noisy, with means 1 and 1/2 and positive gap 1/2.
noncomputable def law (arm : Fin 2) : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac 0 +
    (1/2 : ℝ≥0∞) • Measure.dirac (if arm = 0 then 2 else 1)

instance law_probability (arm : Fin 2) : IsProbabilityMeasure (law arm) := by
  constructor
  norm_num [law, ENNReal.inv_two_add_inv_two]

noncomputable def kernel : Kernel (Fin 2) ℝ := Kernel.ofFunOfCountable law

instance kernel_markov : IsMarkovKernel kernel := by
  constructor
  intro arm
  exact law_probability arm

theorem integrable_law (arm : Fin 2) (g : ℝ → ℝ) : Integrable g (law arm) := by
  simp only [law, integrable_add_measure]
  constructor <;> exact (integrable_dirac (by finiteness)).smul_measure (by norm_num)

theorem law_integral (arm : Fin 2) (g : ℝ → ℝ) :
    (∫ x, g x ∂law arm) = (1/2 : ℝ)*g 0 + (1/2 : ℝ)*g (if arm = 0 then 2 else 1) := by
  rw [law, integral_add_measure]
  · norm_num [integral_smul_measure]
  · exact (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  · exact (integrable_dirac (by finiteness)).smul_measure (by norm_num)

example : realKernelMean kernel 0 - realKernelMean kernel 1 = 1/2 := by
  norm_num [realKernelMean, kernel, Kernel.ofFunOfCountable, law_integral]

theorem moment (arm : Fin 2) : (∫ x, |x|^(1+(1 : ℝ)) ∂kernel arm) ≤ 2 := by
  change (∫ x, |x|^(1+(1 : ℝ)) ∂law arm) ≤ 2
  rw [law_integral]
  by_cases ha : arm = 0 <;> norm_num [ha, Real.rpow_two]

-- T=100, epsilon=1, u=2: actual policy and product reward law, no supplied confidence premise.
example : (∫ stream, realMeanRegret (realKernelMean kernel)
    (robustAction (K := 2) (by decide) 1 2 stream) 100 ∂UCB.armStreamMeasure kernel) ≤
    ∑ arm : Fin 2, realMeanGap (realKernelMean kernel) arm *
      (gapThreshold 1 2 (realMeanGap (realKernelMean kernel) arm) 100 + 2) := by
  apply robust_expected_regret (by decide) kernel 1 2 100 (by norm_num) (by norm_num) (by norm_num)
  · intro arm
    exact integrable_law arm _
  · exact moment

#print axioms BanditRLProof.HeavyTail.robust_expected_regret
#print axioms BanditRLProof.HeavyTail.robust_integral_count_le
#print axioms BanditRLProof.HeavyTail.scheduled_tail_sum_le_two

end HeavyTailRegretCanary
