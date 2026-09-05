import BanditRLProof.ConcentrationMartingaleMaximal

open BanditRLProof MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, StronglyMeasurable (X i))
    (hind : iIndepFun X μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (hsubG : ∀ i, HasSubgaussianMGF (X i) c μ)
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ∃ i, i ≤ n ∧ ε ≤ ∑ j ∈ range i, X (j + 1) ω} ≤
      ENNReal.ofReal (exp (-(ε ^ 2) / (2 * (n : ℝ) * (c : ℝ)))) :=
  Concentration.measure_exists_le_independent_partialSum_ge_le_subgaussian
    X hXm hind hmean c hc hsubG n hn ε hε

#print axioms Concentration.submartingale_exp_of_martingale
#print axioms Concentration.measure_exists_le_martingale_ge_le_exp
#print axioms Concentration.measure_exists_le_martingale_ge_le_subgaussian
#print axioms Concentration.measure_exists_le_independent_partialSum_ge_le_subgaussian
