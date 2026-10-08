import Tests.OnlineFTLLimitSemanticsCanary
open Filter BanditRL.OnlineLearning
namespace ActualFTLValues

def Q1 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ),
    0 ≤ comparatorRegret (fun t x => (x - y t)^2)
      (meanPredict y) (empiricalMean y T) T

theorem wholePublicValue1 : Q1 := @BanditRL.OnlineLearning.meanPredict_bestLoss_nonneg
#check wholePublicValue1
#print axioms wholePublicValue1

def Q2 : Prop := ∀ (y : ℕ → ℝ) (u : ℝ) (T : ℕ),
    comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T =
      comparatorRegret (fun t x => (x - y t)^2)
        (meanPredict y) (empiricalMean y T) T -
      (T : ℝ) * (u - empiricalMean y T)^2

theorem wholePublicValue2 : Q2 := @BanditRL.OnlineLearning.meanPredict_comparator_decomposition
#check wholePublicValue2
#print axioms wholePublicValue2

def Q3 : Prop := ∀ (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1),
    Tendsto (fun T : ℕ => squaredBestRegret y (meanPredict y) T / (T : ℝ))
      atTop (nhds (0 : ℝ))

theorem wholePublicValue3 : Q3 := @BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero
#check wholePublicValue3
#print axioms wholePublicValue3

def Q4 : Prop := ∀ (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) (u a : ℝ),
    Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T / (T : ℝ))
      atTop (nhds a) ↔
    Tendsto (fun T : ℕ => (u - empiricalMean y T)^2) atTop (nhds (-a))

theorem wholePublicValue4 : Q4 := @BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff
#check wholePublicValue4
#print axioms wholePublicValue4

def Q5 : Prop := ∀ (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) (m : ℝ)
    (hm : Tendsto (empiricalMean y) atTop (nhds m)),
    (∀ u : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T / (T : ℝ))
      atTop (nhds (-(u - m)^2))) ∧
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2) (meanPredict y)

theorem wholePublicValue5 : Q5 := @BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges
#check wholePublicValue5
#print axioms wholePublicValue5

end ActualFTLValues

#check BanditRL.OnlineLearning.meanPredict_bestLoss_nonneg
#print axioms BanditRL.OnlineLearning.meanPredict_bestLoss_nonneg
#check BanditRL.OnlineLearning.meanPredict_comparator_decomposition
#print axioms BanditRL.OnlineLearning.meanPredict_comparator_decomposition
#check BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero
#print axioms BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero
#check BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff
#print axioms BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff
#check BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges
#print axioms BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges
#check Tests.OnlineFTLLimitSemantics.alternating_unit
#print axioms Tests.OnlineFTLLimitSemantics.alternating_unit
#check Tests.OnlineFTLLimitSemantics.alternating_prefix_sum
#print axioms Tests.OnlineFTLLimitSemantics.alternating_prefix_sum
#check Tests.OnlineFTLLimitSemantics.alternating_mean_tendsto
#print axioms Tests.OnlineFTLLimitSemantics.alternating_mean_tendsto
#check Tests.OnlineFTLLimitSemantics.alternating_initial_predictions
#print axioms Tests.OnlineFTLLimitSemantics.alternating_initial_predictions
#check Tests.OnlineFTLLimitSemantics.alternating_best_regret_zero_one_two
#print axioms Tests.OnlineFTLLimitSemantics.alternating_best_regret_zero_one_two
#check Tests.OnlineFTLLimitSemantics.alternating_actual_gap_nonneg
#print axioms Tests.OnlineFTLLimitSemantics.alternating_actual_gap_nonneg
#check Tests.OnlineFTLLimitSemantics.alternating_fixed_decomposition
#print axioms Tests.OnlineFTLLimitSemantics.alternating_fixed_decomposition
#check Tests.OnlineFTLLimitSemantics.alternating_best_average_zero
#print axioms Tests.OnlineFTLLimitSemantics.alternating_best_average_zero
#check Tests.OnlineFTLLimitSemantics.alternating_fixed_limit_criterion
#print axioms Tests.OnlineFTLLimitSemantics.alternating_fixed_limit_criterion
#check Tests.OnlineFTLLimitSemantics.alternating_fixed_zero_negative_limit
#print axioms Tests.OnlineFTLLimitSemantics.alternating_fixed_zero_negative_limit
#check Tests.OnlineFTLLimitSemantics.alternating_fixed_half_zero_limit
#print axioms Tests.OnlineFTLLimitSemantics.alternating_fixed_half_zero_limit
#check Tests.OnlineFTLLimitSemantics.alternating_literal_limit_noRegret
#print axioms Tests.OnlineFTLLimitSemantics.alternating_literal_limit_noRegret
#check BanditRL.OnlineLearning.empiricalMean
#print axioms BanditRL.OnlineLearning.empiricalMean
#check BanditRL.OnlineLearning.meanPredict
#print axioms BanditRL.OnlineLearning.meanPredict
#check BanditRL.OnlineLearning.empiricalMean_minimizes
#print axioms BanditRL.OnlineLearning.empiricalMean_minimizes
#check BanditRL.OnlineLearning.empiricalMean_decomposition
#print axioms BanditRL.OnlineLearning.empiricalMean_decomposition
#check BanditRL.OnlineLearning.squaredLoss_minimum_eq
#print axioms BanditRL.OnlineLearning.squaredLoss_minimum_eq
#check BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret
#print axioms BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret
#check BanditRL.OnlineLearning.meanPredict_bestRegret_bound
#print axioms BanditRL.OnlineLearning.meanPredict_bestRegret_bound
