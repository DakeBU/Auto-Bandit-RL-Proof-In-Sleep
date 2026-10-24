import BanditRLProof.OnlineGuessingCompletedCausal
import Tests.OnlineGuessingAECausalCanary

noncomputable section
open MeasureTheory ProbabilityTheory Filter BanditRL.OnlineLearning
open Tests.OnlineGuessingRandomizedIID Tests.OnlineGuessingAECausal

namespace Tests.OnlineGuessingCompletedCausal

theorem bad_completed_measurable (t : ℕ) :
    @Measurable _ _
      (eventuallyMeasurableSpace (privateSeedPastInformation seed target t) (ae seededLaw)) _
      (badPrediction t) :=
  (causal_version_measurable t).eventuallyMeasurable_of_eventuallyEq (bad_eq_causal_ae t)

theorem bad_completed_but_not_ordinary_at_zero :
    (@Measurable _ _
      (eventuallyMeasurableSpace (privateSeedPastInformation seed target 0) (ae seededLaw)) _
      (badPrediction 0)) ∧
      ¬ Measurable[privateSeedPastInformation seed target 0] (badPrediction 0) :=
  ⟨bad_completed_measurable 0, bad_is_not_pointwise_predictable⟩

theorem actual_completed_real_version (t : ℕ) :
    ∃ version : (ℝ × (ℕ → ℝ)) → ℝ,
      Measurable[privateSeedPastInformation seed target t] version ∧
      badPrediction t =ᶠ[ae seededLaw] version :=
  completed_measurable_real_exists_version seededLaw (privateSeedPastInformation seed target t)
    (badPrediction t) (bad_completed_measurable t)

theorem actual_all_time_bounded_policy :
    ∃ policy : (t : ℕ) → (ℝ × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
      (∀ t, Measurable (policy t)) ∧
      (∀ t q, policy t q ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ ω ∂seededLaw, ∀ t, badPrediction t ω = policy t (seed ω, fun i => target i ω) :=
  completed_predictable_exists_bounded_history_policy seededLaw target seed
    (privateSeedPastInformation seed target) (fun _ => le_rfl)
    badPrediction bad_completed_measurable bad_ae_unit

theorem actual_current_independence (t : ℕ) :
    IndepFun (badPrediction t) (target t) seededLaw :=
  completed_predictable_private_seed_independent seededLaw target target_measurable target_independent
    seed seed_measurable seed_independent_whole_process t
    (privateSeedPastInformation seed target t) le_rfl (badPrediction t) (bad_completed_measurable t)

theorem actual_original_excess_identity (T : ℕ) :
    expectedFixedRegret seededLaw target badPrediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (badPrediction t ω - ∫ ω, target 0 ω ∂seededLaw)^2 ∂seededLaw) ∧
      0 ≤ expectedFixedRegret seededLaw target badPrediction T :=
  completed_predictable_private_seed_expectedFixed_excess seededLaw target target_measurable
    target_sameLaw target_support target_independent seed seed_measurable
    seed_independent_whole_process (privateSeedPastInformation seed target) (fun _ => le_rfl)
    badPrediction bad_completed_measurable bad_ae_unit T

theorem actual_nonzero_excess (T : ℕ) :
    expectedFixedRegret seededLaw target badPrediction T = (T : ℝ) / 4 := by
  rw [(actual_original_excess_identity T).1]
  simp_rw [actual_mean_square]
  simp
  ring

theorem actual_two_round_excess :
    expectedFixedRegret seededLaw target badPrediction 2 = 1 / 2 := by
  rw [actual_nonzero_excess]
  norm_num

theorem actual_empty_excess :
    expectedFixedRegret seededLaw target badPrediction 0 = 0 := by
  rw [actual_nonzero_excess]
  norm_num

theorem actual_positive_target_variance : variance (target 0) seededLaw = 1 / 4 :=
  target_variance 0

theorem bad_still_not_everywhere_unit :
    ¬ (∀ t ω, badPrediction t ω ∈ Set.Icc (0 : ℝ) 1) :=
  bad_is_not_everywhere_unit

end Tests.OnlineGuessingCompletedCausal
