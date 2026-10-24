import BanditRLProof.OnlineFTLOscillation

open Filter BanditRL.OnlineLearning
namespace Tests.OnlineFTLOscillation


theorem dyadic_unit_and_prefix :
    (∀ t, dyadicObservation t ∈ Set.Icc (0 : ℝ) 1) ∧
    dyadicObservation 0 = 0 ∧ dyadicObservation 1 = 1 ∧
    dyadicObservation 2 = 1 ∧ dyadicObservation 3 = 0 := by
  refine ⟨dyadicObservation_unit, ?_⟩
  norm_num [dyadicObservation]

theorem actual_causal_predictions :
    meanPredict dyadicObservation 0 = (1 : ℝ)/2 ∧
    meanPredict dyadicObservation 1 = 0 ∧
    meanPredict dyadicObservation 2 = (1 : ℝ)/2 ∧
    meanPredict dyadicObservation 3 = (2 : ℝ)/3 := by
  norm_num [meanPredict, empiricalMean, dyadicObservation, Finset.sum_range_succ]

theorem actual_signed_regrets :
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 0 = 0 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 1 = (1 : ℝ)/4 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 2 = (3 : ℝ)/4 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 3 = (5 : ℝ)/6 ∧
    comparatorRegret (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) 0 3 / (3 : ℝ) = -(1 : ℝ)/6 := by
  have heq (T : ℕ) := squaredBestRegret_eq_comparatorRegret dyadicObservation
    (meanPredict dyadicObservation) T (fun t _ => dyadicObservation_unit t)
  rw [heq 0, heq 1, heq 2, heq 3]
  norm_num [comparatorRegret, meanPredict, empiricalMean, dyadicObservation, Finset.sum_range_succ]

theorem all_comparator_iff_instantiated :
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ↔
    ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean dyadicObservation) atTop (nhds m) := by
  exact meanPredict_limitNoRegret_iff_mean_converges dyadicObservation dyadicObservation_unit

theorem no_feasible_mean_limit :
    ¬ ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean dyadicObservation) atTop (nhds m) := by
  intro h
  exact dyadic_meanPredict_obstruction.2.2.2 (all_comparator_iff_instantiated.mpr h)

theorem two_actual_mean_subsequences :
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (4^(n + 1) - 1))
      atTop (nhds ((2 : ℝ)/3)) ∧
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (2 * 4^n - 1))
      atTop (nhds ((1 : ℝ)/3)) := by
  exact dyadic_empiricalMean_subsequences

theorem obstruction_instantiated :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ∧
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) := by
  exact dyadic_meanPredict_obstruction

theorem upper_noRegret_on_actual_stream :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) := by
  exact dyadic_meanPredict_obstruction.1

theorem actual_best_average_zero :
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) := by
  exact dyadic_meanPredict_obstruction.2.1

theorem fixed_zero_has_no_ordinary_limit :
    ¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a) := by
  exact dyadic_meanPredict_obstruction.2.2.1

theorem literal_limit_noRegret_fails :
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) := by
  exact dyadic_meanPredict_obstruction.2.2.2

end Tests.OnlineFTLOscillation
