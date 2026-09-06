import BanditRLProof.LowerBounds.FiniteDiscreteKL

namespace BanditRLProof.LowerBounds

open MeasureTheory

/-- The sum of two finite laws supplies the common dominating measure in the source. -/
theorem exists_commonFiniteDominatingMeasure {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∃ μ : Measure α, IsFiniteMeasure μ ∧ P ≪ μ ∧ Q ≪ μ := by
  refine ⟨P + Q, inferInstance, ?_, ?_⟩
  · intro s h
    have he : P s + Q s = 0 := by simpa using h
    exact (add_eq_zero.mp he).1
  · intro s h
    have he : P s + Q s = 0 := by simpa using h
    exact (add_eq_zero.mp he).2

theorem exists_commonSigmaFiniteDominatingMeasure {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∃ μ : Measure α, SigmaFinite μ ∧ P ≪ μ ∧ Q ≪ μ := by
  obtain ⟨μ, hμ, hP, hQ⟩ := exists_commonFiniteDominatingMeasure P Q
  letI := hμ
  exact ⟨μ, inferInstance, hP, hQ⟩

/-- Absolute continuity suffices for finite KL on a finite alphabet, not in general. -/
theorem relativeEntropy_finite_lt_top_iff_ac {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    relativeEntropy P Q < ⊤ ↔ P ≪ Q := by
  rw [lt_top_iff_ne_top, ne_eq, relativeEntropy_finite_eq_top_iff,
    absolutelyContinuous_iff_atom_support]
  push Not
  constructor
  · intro h x hq
    by_contra hp
    exact h x hp hq
  · intro h x hp hq
    exact hp (h x hq)

end BanditRLProof.LowerBounds
