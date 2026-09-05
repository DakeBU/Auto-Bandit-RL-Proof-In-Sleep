import BanditRLProof.Algorithms.MOSSPeeling

open BanditRLProof MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, StronglyMeasurable (X i))
    (hind : iIndepFun X μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) :
    μ {ω | ∃ s : ℕ, 0 < s ∧ (∑ j ∈ Finset.range s, X (j+1) ω) / (s : ℝ) +
      sqrt (4 / (s : ℝ) * MOSS.logPlus (1 / ((s : ℝ)*δ))) + gap ≤ 0} ≤
      ENNReal.ofReal (15*δ/gap^2) :=
  MOSS.measure_meanBadEvent_le_fifteen X hXm hind hmean hsubG δ gap hδ hg

#print axioms Concentration.tsum_moss_peeling_exponential_le_fifteen
#print axioms MOSS.measure_blockBadEvent_le
#print axioms MOSS.measure_scaledBadEvent_le_fifteen
#print axioms MOSS.measure_meanBadEvent_le_fifteen
