import BanditRLProof.OnlineFTLInitializationRegret
import Tests.OnlineLearningChapterOneCanary
import Tests.OnlineLearningRegretDomainsCanary
import Tests.OnlineSquareMinimumCanary
import Tests.OnlineGuessingIIDSuccessCanary
import Tests.OnlineGuessingKernelCausalCanary
import Tests.OnlineFTLOscillationCanary
import Tests.OnlineGuessingLogLowerCanary

noncomputable section
open Filter Asymptotics MeasureTheory ProbabilityTheory BanditRL.OnlineLearning
open scoped ENNReal
open Tests.OnlineGuessingIIDBenchmark
namespace Tests.OnlineLearningChapterAudit

def rising (t : ℕ) : ℝ := if t = 0 then 0 else 1
def falling (t : ℕ) : ℝ := if t = 0 then 1 else 0

private theorem rising_mem (t : ℕ) : rising t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold rising
  split_ifs <;> norm_num

private theorem falling_mem (t : ℕ) : falling t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold falling
  split_ifs <;> norm_num

theorem initial_zero_first_regret :
    squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 = 1 ∧
      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 > (1 : ℝ) / 4 := by
  have h : squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 = 1 := by
    rw [squaredBestRegret_eq_comparatorRegret _ _ _ (by intros; norm_num)]
    norm_num [comparatorRegret, ftlPredict, empiricalMean, Finset.sum_range_succ]
  exact ⟨h, by rw [h]; norm_num⟩

theorem two_round_initial_correction :
    squaredBestRegret falling (ftlPredict 0 falling) 2 =
      squaredBestRegret falling (meanPredict falling) 2 + (3 : ℝ) / 4 := by
  have h := ftlPredict_bestRegret_initial_correction 0 falling 2 (by omega)
  norm_num [falling] at h
  exact h

theorem positive_regret_negative_correction :
    squaredBestRegret rising (ftlPredict 0 rising) 2 = (1 : ℝ) / 2 ∧
      squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧
      ((0 - rising 0)^2 - ((1 : ℝ) / 2 - rising 0)^2) = -(1 : ℝ) / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (fun t _ => rising_mem t)]
    norm_num [comparatorRegret, ftlPredict, empiricalMean, rising, Finset.sum_range_succ]
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (fun t _ => rising_mem t)]
    norm_num [comparatorRegret, meanPredict, empiricalMean, rising, Finset.sum_range_succ]
  · norm_num [rising]

theorem general_initial_finite_values :
    squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2 ∧
      squaredBestRegret falling (ftlPredict 0 falling) 2 ≤ (3 : ℝ) ∧
      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (fun t _ => falling_mem t)]
    norm_num [comparatorRegret, ftlPredict, empiricalMean, falling, Finset.sum_range_succ]
  · have h := ftlPredict_bestRegret_refined 0 falling 2 (by omega) (by norm_num)
      (fun t _ => falling_mem t)
    norm_num [Finset.sum_range_succ] at h
    exact h
  · have h := ftlPredict_bestRegret_refined 0 (fun _ => (1 : ℝ)) 1 (by omega)
      (by norm_num) (by intros; norm_num)
    norm_num at h
    exact h

theorem same_past_current_reveal :
    ftlState 0 rising 1 = ftlState 0 (fun _ => 0) 1 ∧
      rising 1 ≠ (0 : ℝ) ∧ ftlState 0 rising 2 ≠ ftlState 0 (fun _ => 0) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply ftlState_prefix
    intro i hi
    have : i = 0 := by omega
    subst i
    norm_num [rising]
  · norm_num [rising]
  · norm_num [ftlState_eq_predict, ftlPredict, empiricalMean, rising, Finset.sum_range_succ]

theorem initialized_state_values :
    ftlState ((3 : ℝ) / 4) rising 0 = (0, (3 : ℝ) / 4) ∧
      ftlState ((3 : ℝ) / 4) rising 1 = (1, 0) ∧
      ftlState ((3 : ℝ) / 4) rising 2 = (2, (1 : ℝ) / 2) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [ftlState_first]
    norm_num [rising]
  · rw [ftlState_eq_predict]
    norm_num [ftlPredict, empiricalMean, rising, Finset.sum_range_succ]

theorem all_initial_dyadic_upper :
    ∀ initial ∈ Set.Icc (0 : ℝ) 1,
      NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
        (ftlPredict initial dyadicObservation) := by
  intro initial hi
  exact ftlPredict_upperNoRegret initial dyadicObservation hi dyadicObservation_unit

theorem nonhalf_dyadic_best_average :
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (ftlPredict ((3 : ℝ) / 4) dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) := by
  exact ftlPredict_bestRegret_average_tendsto_zero ((3 : ℝ) / 4) dyadicObservation
    (by norm_num) dyadicObservation_unit

theorem outside_real_initial_identity :
    squaredBestRegret (fun _ => (3 : ℝ)) (ftlPredict 2 (fun _ => 3)) 1 =
      squaredBestRegret (fun _ => (3 : ℝ)) (meanPredict (fun _ => 3)) 1 - (21 : ℝ) / 4 := by
  have h := ftlPredict_bestRegret_initial_correction 2 (fun _ => (3 : ℝ)) 1 (by omega)
  norm_num at h
  linarith

theorem empty_horizon_not_first_correction :
    squaredBestRegret falling (ftlPredict 0 falling) 0 = 0 ∧
      squaredBestRegret falling (meanPredict falling) 0 = 0 ∧
      ((0 - falling 0)^2 - ((1 : ℝ) / 2 - falling 0)^2) = (3 : ℝ) / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (by intros; omega)]
    simp [comparatorRegret]
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (by intros; omega)]
    simp [comparatorRegret]
  · norm_num [falling]

theorem best_and_fixed_comparator_distinct :
    comparatorRegret (fun t x => (x - falling t)^2) (ftlPredict 0 falling) 0 2 = 1 ∧
      squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2 := by
  refine ⟨?_, general_initial_finite_values.1⟩
  norm_num [comparatorRegret, ftlPredict, empiricalMean, falling, Finset.sum_range_succ]

theorem positive_iid_variance_excess :
    variance (observation 0) iidLaw = (1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 / (2 : ℝ) = (1 : ℝ) / 8 := by
  refine ⟨observation_variance 0, meanPredict_two_round_excess, ?_⟩
  rw [meanPredict_two_round_excess]
  norm_num

theorem population_mean_fixed_minimum :
    IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range 2, (u - observation t ω)^2 ∂iidLaw)
      '' Set.Icc (0 : ℝ) 1) ((1 : ℝ) / 2) ∧
      expectedFixedRegret iidLaw observation (fun _ _ => (1 / 2 : ℝ)) 2 = 0 := by
  exact ⟨actual_mean_attainment, constant_known_mean_zero 2⟩

theorem expectation_and_hindsight_distinct :
    (∫ ω, hindsightMinimum ω 2 ∂iidLaw) = (1 : ℝ) / 4 ∧
      expectedFixedMinimum iidLaw observation 2 = (1 : ℝ) / 2 := by
  exact ⟨hindsight_minimum_two, two_round_fixed_minimum⟩

theorem iid_success_total_and_average :
    Tendsto (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T /
      (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T) =o[atTop]
        (fun T : ℕ => (T : ℝ)) := by
  exact Tests.OnlineGuessingIIDSuccess.actual_meanPredict_success

theorem loss_sequence_visible_outside_comparators :
    (RegretDomainsProbe.output 0).val ∈ RegretDomainsProbe.outputW ∧
      (RegretDomainsProbe.output 0).val ∉ RegretDomainsProbe.sourceV ∧
      comparatorRegret RegretDomainsProbe.domainLoss RegretDomainsProbe.output
        RegretDomainsProbe.referenceOne 2 = -2 ∧
      comparatorRegret (fun t x => 2 * RegretDomainsProbe.domainLoss t x)
        RegretDomainsProbe.output RegretDomainsProbe.referenceOne 2 = -4 := by
  have h := RegretDomainsProbe.outside_prediction_and_negative_regret
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  norm_num [comparatorRegret, RegretDomainsProbe.domainLoss, RegretDomainsProbe.output,
    RegretDomainsProbe.referenceOne, Finset.sum_range_succ]

theorem produced_minimum_and_empty_nonunique :
    empiricalMean rising 2 = (1 : ℝ) / 2 ∧
      sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - rising t)^2) '' Set.Icc (0 : ℝ) 1) = (1 : ℝ) / 2 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, (∑ t ∈ Finset.range 0, (u - rising t)^2) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [empiricalMean, rising, Finset.sum_range_succ]
  · rw [squaredLoss_minimum_eq rising 2 (fun t _ => rising_mem t)]
    norm_num [empiricalMean, rising, Finset.sum_range_succ]
  · intros
    simp

theorem positive_prefix_unique :
    ∀ u : ℝ,
      (∑ t ∈ Finset.range 2, (u - rising t)^2) ≤
        (∑ t ∈ Finset.range 2, (empiricalMean rising 2 - rising t)^2) → u = (1 : ℝ) / 2 := by
  intro u hu
  exact (empiricalMean_unique rising 2 (by omega) u hu).trans
    produced_minimum_and_empty_nonunique.1

theorem concrete_be_the_leader :
    (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) = -2 ∧
      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2)) = 0 ∧
      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) ≤
        ∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [ChapterOneCase0.demoLoss, ChapterOneCase0.demoLeader, Finset.sum_range_succ]
  · norm_num [ChapterOneCase0.demoLoss, ChapterOneCase0.demoLeader, Finset.sum_range_succ]
  · apply lemma_1_2 Set.univ ChapterOneCase0.demoLoss ChapterOneCase0.demoLeader 2
    · simp
    · intro n hn hnt u hu
      interval_cases n <;> cases u <;>
        norm_num [ChapterOneCase0.demoLoss, ChapterOneCase0.demoLeader, Finset.sum_range_succ]

theorem half_refined_and_logarithmic :
    squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧
      squaredBestRegret rising (meanPredict rising) 2 ≤ (9 : ℝ) / 4 ∧
      squaredBestRegret rising (meanPredict rising) 2 ≤ 4 + 4 * Real.log 2 := by
  refine ⟨positive_regret_negative_correction.2.1, ?_, ?_⟩
  · have h := meanPredict_bestRegret_refined rising 2 (by omega) (fun t _ => rising_mem t)
    norm_num [Finset.sum_range_succ] at h
    exact h
  · exact meanPredict_bestRegret_bound rising 2 (by omega) (fun t _ => rising_mem t)

theorem same_stream_later_stability :
    (meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 = (3 : ℝ) / 4 ∧
      (meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 ≤ 4 / ((1 : ℝ) + 1) := by
  refine ⟨?_, ?_⟩
  · norm_num [meanPredict, empiricalMean, rising, Finset.sum_range_succ]
  · change (meanPredict rising 1 - rising 1)^2 - (empiricalMean rising 2 - rising 1)^2 ≤
      4 / ((1 : ℝ) + 1)
    simpa only [Nat.cast_one] using meanPredict_stability rising 1 (fun i _ => rising_mem i)

theorem actual_kernel_same_run_excess :
    (∀ T : ℕ, expectedFixedRegret Tests.OnlineGuessingKernelCausal.gameLaw
      Tests.OnlineGuessingKernelCausal.target
      (fun t ω => (Tests.OnlineGuessingKernelCausal.prediction t ω : ℝ)) T = (T : ℝ) / 4) ∧
      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 0 1) {1} = (1 / 4 : ℝ≥0∞) ∧
      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 1 1) {1} = (3 / 4 : ℝ≥0∞) := by
  exact ⟨Tests.OnlineGuessingKernelCausal.every_horizon_excess,
    Tests.OnlineGuessingKernelCausal.history_feedback_distribution.1,
    Tests.OnlineGuessingKernelCausal.history_feedback_distribution.2.1⟩

theorem correlation_changes_excess :
    expectedFixedRegret iidLaw (fun _ => observation 0)
      (fun t ω => meanPredict (fun _ => observation 0 ω) t) 2 = -(1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4 := by
  exact ⟨Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_negative_two,
    meanPredict_two_round_excess⟩

theorem same_actual_ftl_limit_obstruction :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation) ∧
      Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (¬ ∃ a : ℝ, Tendsto (fun T : ℕ => comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation) := by
  exact dyadic_meanPredict_obstruction

theorem qualitative_log_fixed_binary_witness :
    ∃ v : List.Vector Bool 2, Real.log 4 / 6 ≤
      ∫ b, BanditRL.OnlineLearning.GuessingLower.pathRegret (GuessingLogLowerProbe.seededPolicy b) v.toList
        ∂GuessingLogLowerProbe.coinMeasure := by
  exact GuessingLogLowerProbe.seeded_log_endpoint

theorem harmonic_two_bound :
    (harmonic 2 : ℝ) = (3 : ℝ) / 2 ∧ (harmonic 2 : ℝ) ≤ 1 + Real.log 2 := by
  refine ⟨?_, harmonic_le_one_add_log 2⟩
  norm_num [harmonic, Finset.sum_range_succ]

theorem centered_total_average_boundary :
    (fun T : ℕ => (5 + 3 * (T : ℝ)) - (T : ℝ) * 3) =o[atTop]
      (fun T : ℕ => (T : ℝ)) ∧
      ((5 + 3 * (0 : ℝ)) / (0 : ℝ) - 3) = -(3 : ℝ) := by
  exact ⟨Tests.OnlineGuessingIIDSuccess.nonzero_initial_total_sublinear, by norm_num⟩

end Tests.OnlineLearningChapterAudit
