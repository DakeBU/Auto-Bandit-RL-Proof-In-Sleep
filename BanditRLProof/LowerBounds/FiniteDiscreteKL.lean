import BanditRLProof.LowerBounds.InformationTheory
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace BanditRLProof.LowerBounds

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Atomwise density identity, retaining zero-mass atoms. -/
theorem rnDeriv_mul_atom {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≪ Q) (x : α) :
    P.rnDeriv Q x * Q {x} = P {x} := by
  have heq := congrArg (fun μ : Measure α => μ {x})
    (Measure.withDensity_rnDeriv_eq P Q h)
  simpa [mul_comm] using heq

/-- On a positive reference atom, the RN density is the atom-mass ratio. -/
theorem rnDeriv_atom_eq_div {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≪ Q) (x : α)
    (hq : Q {x} ≠ 0) : P.rnDeriv Q x = P {x} / Q {x} := by
  exact (ENNReal.eq_div_iff hq (measure_ne_top Q {x})).2
    (by simpa [mul_comm] using rnDeriv_mul_atom P Q h x)

/-- A positive source atom absent from the reference law forces infinite KL. -/
theorem relativeEntropy_eq_top_of_atom_support_mismatch {α : Type*}
    [MeasurableSpace α] (P Q : Measure α) (x : α)
    (hp : P {x} ≠ 0) (hq : Q {x} = 0) : relativeEntropy P Q = ∞ := by
  apply InformationTheory.klDiv_of_not_ac
  intro h
  exact hp (h hq)

/-- Finite-alphabet KL in its nonnegative convex-integrand form. -/
theorem relativeEntropy_finite_klFun {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≪ Q) :
    relativeEntropy P Q = ∑ x, ENNReal.ofReal
      (InformationTheory.klFun ((P {x} / Q {x}).toReal)) * Q {x} := by
  rw [relativeEntropy, InformationTheory.klDiv_eq_lintegral_klFun_of_ac h,
    lintegral_fintype]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hq : Q {x} = 0
  · simp [hq]
  · rw [rnDeriv_atom_eq_div P Q h x hq]

/-- Textbook Eq. (14.4) on any finite alphabet in the supported branch. -/
theorem relativeEntropy_finite_sum_log {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : P ≪ Q) :
    relativeEntropy P Q = ENNReal.ofReal
      (∑ x, (P {x}).toReal * Real.log ((P {x}).toReal / (Q {x}).toReal)) := by
  have hi : Integrable (llr P Q) P :=
    (SimpleFunc.ofFinite (llr P Q)).integrable_of_isFiniteMeasure
  rw [relativeEntropy_of_probability_absolutelyContinuous_of_integrable P Q h hi,
    integral_fintype hi]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P {x} = 0
  · simp [measureReal_def, hp]
  · have hq : Q {x} ≠ 0 := fun hz => hp (h hz)
    simp [llr, rnDeriv_atom_eq_div P Q h x hq, ENNReal.toReal_div,
      measureReal_def, smul_eq_mul]

end
end BanditRLProof.LowerBounds
