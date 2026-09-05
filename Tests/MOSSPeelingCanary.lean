import BanditRLProof.Algorithms.MOSSPeeling
import BanditRLProof.Algorithms.MOSSOptimism
import BanditRLProof.Algorithms.MOSSOccupancy
import BanditRLProof.ConcentrationGaussianOccupancy

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

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ : ℝ) (n : ℕ) :
    ∫ ω, MOSS.optimismDeficit X δ n ω ∂μ =
      ∫ gap in Set.Ioi 0, μ.real {ω | gap ≤ MOSS.optimismDeficit X δ n ω} :=
  MOSS.integral_optimismDeficit_eq_integral_tail X hsubG δ n

#print axioms MOSS.integrable_optimismDeficit
#print axioms MOSS.measure_optimismDeficit_ge_le
#print axioms MOSS.integral_optimismDeficit_eq_integral_tail

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∫ ω, MOSS.optimismDeficit X δ n ω ∂μ ≤ 2*sqrt (15*δ) :=
  MOSS.integral_optimismDeficit_le_two_sqrt X hXm hind hmean hsubG δ hδ n

#print axioms Concentration.integral_positive_tail_le_two_sqrt
#print axioms MOSS.integral_optimismDeficit_le_two_sqrt
#print axioms MOSS.twice_horizon_mul_integral_optimismDeficit_le

example (mean : ℕ → ℝ) (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (n : ℕ) :
    MOSS.indexExceedanceCount mean δ gap n ≤
      1/gap^2 + MOSS.fixedLogExceedanceCount mean δ gap n :=
  MOSS.indexExceedanceCount_le_inv_sq_add_fixed mean δ gap hδ hg n

#print axioms MOSS.sampleRadius_le_fixedLogRadius
#print axioms MOSS.smallSampleCount_le_inv_sq
#print axioms MOSS.indexExceedanceCount_le_inv_sq_add_fixed

example (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∫ z : ℝ in Set.Ioi 0, (2/ε^2)*(z+sqrt (2*a))*exp (-(1/2 : ℝ)*z^2) =
      (2/ε^2)*(1+sqrt (Real.pi*a)) :=
  Concentration.integral_transformed_occupancy_tail a ε ha hε

#print axioms Concentration.integral_mul_exp_neg_mul_sq_Ioi
#print axioms Concentration.integral_transformed_occupancy_tail
#print axioms Concentration.occupancyTail_antitoneOn
