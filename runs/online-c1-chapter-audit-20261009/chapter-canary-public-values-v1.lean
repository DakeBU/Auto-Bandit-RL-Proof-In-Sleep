import Tests.OnlineLearningChapterAuditCanary
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
open Tests.OnlineLearningChapterAudit

#check Tests.OnlineLearningChapterAudit.initial_zero_first_regret
#print axioms Tests.OnlineLearningChapterAudit.initial_zero_first_regret
example :
    squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 = 1 ∧
      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 > (1 : ℝ) / 4 :=
  Tests.OnlineLearningChapterAudit.initial_zero_first_regret

#check Tests.OnlineLearningChapterAudit.two_round_initial_correction
#print axioms Tests.OnlineLearningChapterAudit.two_round_initial_correction
example :
    squaredBestRegret falling (ftlPredict 0 falling) 2 =
      squaredBestRegret falling (meanPredict falling) 2 + (3 : ℝ) / 4 :=
  Tests.OnlineLearningChapterAudit.two_round_initial_correction

#check Tests.OnlineLearningChapterAudit.positive_regret_negative_correction
#print axioms Tests.OnlineLearningChapterAudit.positive_regret_negative_correction
example :
    squaredBestRegret rising (ftlPredict 0 rising) 2 = (1 : ℝ) / 2 ∧
      squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧
      ((0 - rising 0)^2 - ((1 : ℝ) / 2 - rising 0)^2) = -(1 : ℝ) / 4 :=
  Tests.OnlineLearningChapterAudit.positive_regret_negative_correction

#check Tests.OnlineLearningChapterAudit.general_initial_finite_values
#print axioms Tests.OnlineLearningChapterAudit.general_initial_finite_values
example :
    squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2 ∧
      squaredBestRegret falling (ftlPredict 0 falling) 2 ≤ (3 : ℝ) ∧
      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 ≤ 1 :=
  Tests.OnlineLearningChapterAudit.general_initial_finite_values

#check Tests.OnlineLearningChapterAudit.same_past_current_reveal
#print axioms Tests.OnlineLearningChapterAudit.same_past_current_reveal
example :
    ftlState 0 rising 1 = ftlState 0 (fun _ => 0) 1 ∧
      rising 1 ≠ (0 : ℝ) ∧ ftlState 0 rising 2 ≠ ftlState 0 (fun _ => 0) 2 :=
  Tests.OnlineLearningChapterAudit.same_past_current_reveal

#check Tests.OnlineLearningChapterAudit.initialized_state_values
#print axioms Tests.OnlineLearningChapterAudit.initialized_state_values
example :
    ftlState ((3 : ℝ) / 4) rising 0 = (0, (3 : ℝ) / 4) ∧
      ftlState ((3 : ℝ) / 4) rising 1 = (1, 0) ∧
      ftlState ((3 : ℝ) / 4) rising 2 = (2, (1 : ℝ) / 2) :=
  Tests.OnlineLearningChapterAudit.initialized_state_values

#check Tests.OnlineLearningChapterAudit.all_initial_dyadic_upper
#print axioms Tests.OnlineLearningChapterAudit.all_initial_dyadic_upper
example :
    ∀ initial ∈ Set.Icc (0 : ℝ) 1,
      NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
        (ftlPredict initial dyadicObservation) :=
  Tests.OnlineLearningChapterAudit.all_initial_dyadic_upper

#check Tests.OnlineLearningChapterAudit.nonhalf_dyadic_best_average
#print axioms Tests.OnlineLearningChapterAudit.nonhalf_dyadic_best_average
example :
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (ftlPredict ((3 : ℝ) / 4) dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) :=
  Tests.OnlineLearningChapterAudit.nonhalf_dyadic_best_average

#check Tests.OnlineLearningChapterAudit.outside_real_initial_identity
#print axioms Tests.OnlineLearningChapterAudit.outside_real_initial_identity
example :
    squaredBestRegret (fun _ => (3 : ℝ)) (ftlPredict 2 (fun _ => 3)) 1 =
      squaredBestRegret (fun _ => (3 : ℝ)) (meanPredict (fun _ => 3)) 1 - (21 : ℝ) / 4 :=
  Tests.OnlineLearningChapterAudit.outside_real_initial_identity

#check Tests.OnlineLearningChapterAudit.empty_horizon_not_first_correction
#print axioms Tests.OnlineLearningChapterAudit.empty_horizon_not_first_correction
example :
    squaredBestRegret falling (ftlPredict 0 falling) 0 = 0 ∧
      squaredBestRegret falling (meanPredict falling) 0 = 0 ∧
      ((0 - falling 0)^2 - ((1 : ℝ) / 2 - falling 0)^2) = (3 : ℝ) / 4 :=
  Tests.OnlineLearningChapterAudit.empty_horizon_not_first_correction

#check Tests.OnlineLearningChapterAudit.best_and_fixed_comparator_distinct
#print axioms Tests.OnlineLearningChapterAudit.best_and_fixed_comparator_distinct
example :
    comparatorRegret (fun t x => (x - falling t)^2) (ftlPredict 0 falling) 0 2 = 1 ∧
      squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2 :=
  Tests.OnlineLearningChapterAudit.best_and_fixed_comparator_distinct

#check Tests.OnlineLearningChapterAudit.positive_iid_variance_excess
#print axioms Tests.OnlineLearningChapterAudit.positive_iid_variance_excess
example :
    variance (observation 0) iidLaw = (1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 / (2 : ℝ) = (1 : ℝ) / 8 :=
  Tests.OnlineLearningChapterAudit.positive_iid_variance_excess

#check Tests.OnlineLearningChapterAudit.population_mean_fixed_minimum
#print axioms Tests.OnlineLearningChapterAudit.population_mean_fixed_minimum
example :
    IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range 2, (u - observation t ω)^2 ∂iidLaw)
      '' Set.Icc (0 : ℝ) 1) ((1 : ℝ) / 2) ∧
      expectedFixedRegret iidLaw observation (fun _ _ => (1 / 2 : ℝ)) 2 = 0 :=
  Tests.OnlineLearningChapterAudit.population_mean_fixed_minimum

#check Tests.OnlineLearningChapterAudit.expectation_and_hindsight_distinct
#print axioms Tests.OnlineLearningChapterAudit.expectation_and_hindsight_distinct
example :
    (∫ ω, hindsightMinimum ω 2 ∂iidLaw) = (1 : ℝ) / 4 ∧
      expectedFixedMinimum iidLaw observation 2 = (1 : ℝ) / 2 :=
  Tests.OnlineLearningChapterAudit.expectation_and_hindsight_distinct

#check Tests.OnlineLearningChapterAudit.iid_success_total_and_average
#print axioms Tests.OnlineLearningChapterAudit.iid_success_total_and_average
example :
    Tendsto (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T /
      (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T) =o[atTop]
        (fun T : ℕ => (T : ℝ)) :=
  Tests.OnlineLearningChapterAudit.iid_success_total_and_average

#check Tests.OnlineLearningChapterAudit.loss_sequence_visible_outside_comparators
#print axioms Tests.OnlineLearningChapterAudit.loss_sequence_visible_outside_comparators
example :
    (RegretDomainsProbe.output 0).val ∈ RegretDomainsProbe.outputW ∧
      (RegretDomainsProbe.output 0).val ∉ RegretDomainsProbe.sourceV ∧
      comparatorRegret RegretDomainsProbe.domainLoss RegretDomainsProbe.output
        RegretDomainsProbe.referenceOne 2 = -2 ∧
      comparatorRegret (fun t x => 2 * RegretDomainsProbe.domainLoss t x)
        RegretDomainsProbe.output RegretDomainsProbe.referenceOne 2 = -4 :=
  Tests.OnlineLearningChapterAudit.loss_sequence_visible_outside_comparators

#check Tests.OnlineLearningChapterAudit.produced_minimum_and_empty_nonunique
#print axioms Tests.OnlineLearningChapterAudit.produced_minimum_and_empty_nonunique
example :
    empiricalMean rising 2 = (1 : ℝ) / 2 ∧
      sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - rising t)^2) '' Set.Icc (0 : ℝ) 1) = (1 : ℝ) / 2 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, (∑ t ∈ Finset.range 0, (u - rising t)^2) = 0 :=
  Tests.OnlineLearningChapterAudit.produced_minimum_and_empty_nonunique

#check Tests.OnlineLearningChapterAudit.positive_prefix_unique
#print axioms Tests.OnlineLearningChapterAudit.positive_prefix_unique
example :
    ∀ u : ℝ,
      (∑ t ∈ Finset.range 2, (u - rising t)^2) ≤
        (∑ t ∈ Finset.range 2, (empiricalMean rising 2 - rising t)^2) → u = (1 : ℝ) / 2 :=
  Tests.OnlineLearningChapterAudit.positive_prefix_unique

#check Tests.OnlineLearningChapterAudit.concrete_be_the_leader
#print axioms Tests.OnlineLearningChapterAudit.concrete_be_the_leader
example :
    (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) = -2 ∧
      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2)) = 0 ∧
      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) ≤
        ∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2) :=
  Tests.OnlineLearningChapterAudit.concrete_be_the_leader

#check Tests.OnlineLearningChapterAudit.half_refined_and_logarithmic
#print axioms Tests.OnlineLearningChapterAudit.half_refined_and_logarithmic
example :
    squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧
      squaredBestRegret rising (meanPredict rising) 2 ≤ (9 : ℝ) / 4 ∧
      squaredBestRegret rising (meanPredict rising) 2 ≤ 4 + 4 * Real.log 2 :=
  Tests.OnlineLearningChapterAudit.half_refined_and_logarithmic

#check Tests.OnlineLearningChapterAudit.same_stream_later_stability
#print axioms Tests.OnlineLearningChapterAudit.same_stream_later_stability
example :
    (meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 = (3 : ℝ) / 4 ∧
      (meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 ≤ 4 / ((1 : ℝ) + 1) :=
  Tests.OnlineLearningChapterAudit.same_stream_later_stability

#check Tests.OnlineLearningChapterAudit.actual_kernel_same_run_excess
#print axioms Tests.OnlineLearningChapterAudit.actual_kernel_same_run_excess
example :
    (∀ T : ℕ, expectedFixedRegret Tests.OnlineGuessingKernelCausal.gameLaw
      Tests.OnlineGuessingKernelCausal.target
      (fun t ω => (Tests.OnlineGuessingKernelCausal.prediction t ω : ℝ)) T = (T : ℝ) / 4) ∧
      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 0 1) {1} = (1 / 4 : ℝ≥0∞) ∧
      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 1 1) {1} = (3 / 4 : ℝ≥0∞) :=
  Tests.OnlineLearningChapterAudit.actual_kernel_same_run_excess

#check Tests.OnlineLearningChapterAudit.correlation_changes_excess
#print axioms Tests.OnlineLearningChapterAudit.correlation_changes_excess
example :
    expectedFixedRegret iidLaw (fun _ => observation 0)
      (fun t ω => meanPredict (fun _ => observation 0 ω) t) 2 = -(1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4 :=
  Tests.OnlineLearningChapterAudit.correlation_changes_excess

#check Tests.OnlineLearningChapterAudit.same_actual_ftl_limit_obstruction
#print axioms Tests.OnlineLearningChapterAudit.same_actual_ftl_limit_obstruction
example :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation) ∧
      Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (¬ ∃ a : ℝ, Tendsto (fun T : ℕ => comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation) :=
  Tests.OnlineLearningChapterAudit.same_actual_ftl_limit_obstruction

#check Tests.OnlineLearningChapterAudit.qualitative_log_fixed_binary_witness
#print axioms Tests.OnlineLearningChapterAudit.qualitative_log_fixed_binary_witness
example :
    ∃ v : List.Vector Bool 2, Real.log 4 / 6 ≤
      ∫ b, BanditRL.OnlineLearning.GuessingLower.pathRegret (GuessingLogLowerProbe.seededPolicy b) v.toList
        ∂GuessingLogLowerProbe.coinMeasure :=
  Tests.OnlineLearningChapterAudit.qualitative_log_fixed_binary_witness

#check Tests.OnlineLearningChapterAudit.harmonic_two_bound
#print axioms Tests.OnlineLearningChapterAudit.harmonic_two_bound
example :
    (harmonic 2 : ℝ) = (3 : ℝ) / 2 ∧ (harmonic 2 : ℝ) ≤ 1 + Real.log 2 :=
  Tests.OnlineLearningChapterAudit.harmonic_two_bound

#check Tests.OnlineLearningChapterAudit.centered_total_average_boundary
#print axioms Tests.OnlineLearningChapterAudit.centered_total_average_boundary
example :
    (fun T : ℕ => (5 + 3 * (T : ℝ)) - (T : ℝ) * 3) =o[atTop]
      (fun T : ℕ => (T : ℝ)) ∧
      ((5 + 3 * (0 : ℝ)) / (0 : ℝ) - 3) = -(3 : ℝ) :=
  Tests.OnlineLearningChapterAudit.centered_total_average_boundary
