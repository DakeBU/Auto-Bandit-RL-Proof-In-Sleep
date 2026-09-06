import BanditRLProof.LowerBounds.FiniteDiscreteKL
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace BanditRLProof.LowerBounds

open MeasureTheory

noncomputable def discreteCrossEntropy {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ i, p i * Real.log (q i)⁻¹

/-- The unrounded information-cost interpretation of Eq. (14.4). -/
theorem discreteCrossEntropy_sub_entropy {α : Type*} [Fintype α] (p q : α → ℝ)
    (hsupport : ∀ i, p i ≠ 0 → q i ≠ 0) :
    discreteCrossEntropy p q - discreteEntropy Finset.univ p =
      ∑ i, p i * Real.log (p i / q i) := by
  rw [discreteCrossEntropy, discreteEntropy, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i = 0
  · simp [hi]
  · rw [Real.log_inv, Real.log_inv, Real.log_div hi (hsupport i hi)]
    ring

theorem relativeEntropy_finite_crossEntropy {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : P ≪ Q) :
    relativeEntropy P Q = ENNReal.ofReal
      (discreteCrossEntropy (fun i => (P {i}).toReal) (fun i => (Q {i}).toReal) -
        discreteEntropy Finset.univ (fun i => (P {i}).toReal)) := by
  rw [discreteCrossEntropy_sub_entropy]
  · exact relativeEntropy_finite_sum_log P Q h
  · intro i hi
    have hP : P {i} ≠ 0 := by intro hz; simp [hz] at hi
    have hQ : Q {i} ≠ 0 := fun hz => hP (h hz)
    exact ENNReal.toReal_ne_zero.mpr ⟨hQ, measure_ne_top Q {i}⟩

/-- The source's zero-mass entropy convention agrees with the right-hand limit. -/
theorem entropyTerm_tendsto_zero_right :
    Filter.Tendsto (fun x : ℝ => x * Real.log x⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h := Real.continuous_mul_log.continuousAt.tendsto (x := (0 : ℝ))
  have hn := h.neg
  have ht : Filter.Tendsto (fun x : ℝ => x * Real.log x⁻¹) (nhds 0) (nhds 0) := by
    simpa [Real.log_inv] using hn
  exact ht.mono_left nhdsWithin_le_nhds

end BanditRLProof.LowerBounds
