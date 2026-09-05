import BanditRLProof

/-! Root-import canary for the full finite-partition/RN relative entropy equality. -/

namespace BanditRLProof.TextbookPartIVChapter14RecoveryCanary

open MeasureTheory LowerBounds
open scoped ENNReal

example {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    finitePartitionRelativeEntropy P Q = relativeEntropy P Q :=
  finitePartitionRelativeEntropy_eq_relativeEntropy P Q

-- Infinite divergence is retained without an AC or log-integrability premise.
example {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : relativeEntropy P Q = (⊤ : ENNReal)) :
    finitePartitionRelativeEntropy P Q = (⊤ : ENNReal) :=
  (finitePartitionRelativeEntropy_eq_relativeEntropy P Q).trans h

example : finitePartitionRelativeEntropy (Measure.dirac (0 : ℝ))
    (Measure.dirac (0 : ℝ)) = 0 := by
  rw [finitePartitionRelativeEntropy_eq_relativeEntropy]
  exact relativeEntropy_eq_zero_iff.2 rfl

example : finitePartitionRelativeEntropy (Measure.dirac (0 : ℝ))
    (Measure.dirac (1 : ℝ)) = (⊤ : ENNReal) := by
  rw [finitePartitionRelativeEntropy_eq_relativeEntropy]
  apply relativeEntropy_eq_top_of_atom_support_mismatch _ _ (0 : ℝ)
  · simp
  · simp

#print axioms LowerBounds.exists_fin_encoding_of_finite_range
#print axioms LowerBounds.exists_fin_observation_densityApproximation
#print axioms LowerBounds.relativeEntropy_trim_mono
#print axioms LowerBounds.finitePartitionRelativeEntropy_eq_relativeEntropy

end BanditRLProof.TextbookPartIVChapter14RecoveryCanary
