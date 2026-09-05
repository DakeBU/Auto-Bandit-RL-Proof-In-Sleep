import BanditRLProof.LowerBounds.RelativeEntropyFiltration

/-! Focused KL recovery canary; finite observation encoding remains a separate obligation. -/

namespace BanditRLProof.TextbookPartIVChapter14FiltrationCanary

open MeasureTheory LowerBounds
open scoped ENNReal

example {α : Type*} [m : MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≪ Q) :
    (⨆ n, @relativeEntropy α (densityApproximationFiltration (P.rnDeriv Q) n)
      (P.trim ((densityApproximationFiltration (P.rnDeriv Q)).le n))
      (Q.trim ((densityApproximationFiltration (P.rnDeriv Q)).le n))) =
      relativeEntropy P Q :=
  (relativeEntropy_eq_iSup_densityApproximation_trim P Q h).symm

example {α : Type*} [m : MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : P ≪ Q)
    {n : ℕ} (f : α → Fin n) (hf : Measurable f) :
    relativeEntropy (P.map f) (Q.map f) =
      @relativeEntropy α ((inferInstance : MeasurableSpace (Fin n)).comap f)
        (P.trim hf.comap_le) (Q.trim hf.comap_le) :=
  relativeEntropy_map_eq_trim_of_absolutelyContinuous P Q h f hf

#print axioms LowerBounds.relativeEntropy_trim_eq_lintegral_condExp
#print axioms LowerBounds.relativeEntropy_map_eq_trim_of_absolutelyContinuous
#print axioms LowerBounds.relativeEntropy_eq_iSup_trim_of_density_measurable
#print axioms LowerBounds.densityApproximationFiltration
#print axioms LowerBounds.measurable_density_iSup_approximationFiltration
#print axioms LowerBounds.relativeEntropy_eq_iSup_densityApproximation_trim

end BanditRLProof.TextbookPartIVChapter14FiltrationCanary
