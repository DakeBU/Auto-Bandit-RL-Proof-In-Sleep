import BanditRLProof.LowerBounds.FinitePartitionKL

/-! Focused canary for the partial Eq. (14.5) bridge; not a whole-chapter gate. -/

namespace BanditRLProof.TextbookPartIVChapter14PartitionCanary

open MeasureTheory Set LowerBounds
open scoped ENNReal

example {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {n : ℕ} (f : α → Fin n) (hf : Measurable f) :
    relativeEntropy (P.map f) (Q.map f) ≤ relativeEntropy P Q :=
  relativeEntropy_finite_map_le P Q f hf

example {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    (h : ¬ P ≪ Q) : finitePartitionRelativeEntropy P Q = relativeEntropy P Q :=
  finitePartitionRelativeEntropy_eq_relativeEntropy_of_not_absolutelyContinuous P Q h

example : finitePartitionRelativeEntropy (Measure.dirac (0 : Fin 3))
    (Measure.dirac (0 : Fin 3)) = 0 := by
  rw [finitePartitionRelativeEntropy_fin_eq]
  exact relativeEntropy_eq_zero_iff.2 rfl

example : finitePartitionRelativeEntropy (Measure.dirac (0 : Fin 3))
    (Measure.dirac (1 : Fin 3)) = (⊤ : ENNReal) := by
  apply finitePartitionRelativeEntropy_eq_top_of_not_absolutelyContinuous
  intro h
  have hz : (Measure.dirac (1 : Fin 3)) {(0 : Fin 3)} = 0 := by simp
  have hp := h hz
  simpa using hp

#print axioms LowerBounds.totalMass_klFun_le_relativeEntropy
#print axioms LowerBounds.sum_relativeEntropy_restrict_fibers
#print axioms LowerBounds.relativeEntropy_finite_map_le
#print axioms LowerBounds.finitePartitionRelativeEntropy
#print axioms LowerBounds.finitePartitionRelativeEntropy_le_relativeEntropy
#print axioms LowerBounds.relativeEntropy_map_le_finitePartitionRelativeEntropy
#print axioms LowerBounds.finitePartitionRelativeEntropy_fin_eq
#print axioms LowerBounds.relativeEntropy_finite_map_eq_if
#print axioms LowerBounds.exists_binary_map_relativeEntropy_eq_top_of_event
#print axioms LowerBounds.finitePartitionRelativeEntropy_eq_top_of_not_absolutelyContinuous
#print axioms LowerBounds.finitePartitionRelativeEntropy_eq_relativeEntropy_of_not_absolutelyContinuous

end BanditRLProof.TextbookPartIVChapter14PartitionCanary
