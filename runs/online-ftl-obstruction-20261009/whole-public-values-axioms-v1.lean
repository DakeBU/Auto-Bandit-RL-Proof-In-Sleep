import Tests.OnlineFTLOscillationCanary
open Filter BanditRL.OnlineLearning
namespace ActualFTLObstructionValues

def Q1 : Prop := ∀ (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1),
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2) (meanPredict y) ↔
      ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean y) atTop (nhds m)

theorem wholePublicValue1 : Q1 := @BanditRL.OnlineLearning.meanPredict_limitNoRegret_iff_mean_converges
#check wholePublicValue1
#print axioms wholePublicValue1

def Q2 : Prop :=     ∀ t, dyadicObservation t ∈ Set.Icc (0 : ℝ) 1

theorem wholePublicValue2 : Q2 := @BanditRL.OnlineLearning.dyadicObservation_unit
#check wholePublicValue2
#print axioms wholePublicValue2

def Q3 : Prop :=     Tendsto (fun n : ℕ => empiricalMean dyadicObservation (4^(n + 1) - 1))
      atTop (nhds ((2 : ℝ) / 3)) ∧
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (2 * 4^n - 1))
      atTop (nhds ((1 : ℝ) / 3))

theorem wholePublicValue3 : Q3 := @BanditRL.OnlineLearning.dyadic_empiricalMean_subsequences
#check wholePublicValue3
#print axioms wholePublicValue3

def Q4 : Prop :=     NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ∧
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation)

theorem wholePublicValue4 : Q4 := @BanditRL.OnlineLearning.dyadic_meanPredict_obstruction
#check wholePublicValue4
#print axioms wholePublicValue4

end ActualFTLObstructionValues

#check BanditRL.OnlineLearning.meanPredict_limitNoRegret_iff_mean_converges
#print axioms BanditRL.OnlineLearning.meanPredict_limitNoRegret_iff_mean_converges
#check BanditRL.OnlineLearning.dyadicObservation_unit
#print axioms BanditRL.OnlineLearning.dyadicObservation_unit
#check BanditRL.OnlineLearning.dyadic_empiricalMean_subsequences
#print axioms BanditRL.OnlineLearning.dyadic_empiricalMean_subsequences
#check BanditRL.OnlineLearning.dyadic_meanPredict_obstruction
#print axioms BanditRL.OnlineLearning.dyadic_meanPredict_obstruction
#check Tests.OnlineFTLOscillation.dyadic_unit_and_prefix
#print axioms Tests.OnlineFTLOscillation.dyadic_unit_and_prefix
#check Tests.OnlineFTLOscillation.actual_causal_predictions
#print axioms Tests.OnlineFTLOscillation.actual_causal_predictions
#check Tests.OnlineFTLOscillation.actual_signed_regrets
#print axioms Tests.OnlineFTLOscillation.actual_signed_regrets
#check Tests.OnlineFTLOscillation.all_comparator_iff_instantiated
#print axioms Tests.OnlineFTLOscillation.all_comparator_iff_instantiated
#check Tests.OnlineFTLOscillation.no_feasible_mean_limit
#print axioms Tests.OnlineFTLOscillation.no_feasible_mean_limit
#check Tests.OnlineFTLOscillation.two_actual_mean_subsequences
#print axioms Tests.OnlineFTLOscillation.two_actual_mean_subsequences
#check Tests.OnlineFTLOscillation.obstruction_instantiated
#print axioms Tests.OnlineFTLOscillation.obstruction_instantiated
#check Tests.OnlineFTLOscillation.upper_noRegret_on_actual_stream
#print axioms Tests.OnlineFTLOscillation.upper_noRegret_on_actual_stream
#check Tests.OnlineFTLOscillation.actual_best_average_zero
#print axioms Tests.OnlineFTLOscillation.actual_best_average_zero
#check Tests.OnlineFTLOscillation.fixed_zero_has_no_ordinary_limit
#print axioms Tests.OnlineFTLOscillation.fixed_zero_has_no_ordinary_limit
#check Tests.OnlineFTLOscillation.literal_limit_noRegret_fails
#print axioms Tests.OnlineFTLOscillation.literal_limit_noRegret_fails
#check BanditRL.OnlineLearning.empiricalMean
#print axioms BanditRL.OnlineLearning.empiricalMean
#check BanditRL.OnlineLearning.meanPredict
#print axioms BanditRL.OnlineLearning.meanPredict
#check BanditRL.OnlineLearning.dyadicObservation
#print axioms BanditRL.OnlineLearning.dyadicObservation
#check BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff
#print axioms BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff
#check BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges
#print axioms BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges
#check BanditRL.OnlineLearning.meanPredict_noRegret
#print axioms BanditRL.OnlineLearning.meanPredict_noRegret
#check BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero
#print axioms BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero
#check BanditRL.OnlineLearning.empiricalMean_mem
#print axioms BanditRL.OnlineLearning.empiricalMean_mem
#check BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret
#print axioms BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret
