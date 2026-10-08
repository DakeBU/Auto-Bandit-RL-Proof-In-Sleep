import Tests.OnlineGuessingCompletedCausalCanary
open MeasureTheory ProbabilityTheory Filter BanditRL.OnlineLearning
universe u v
namespace NeutralCompletedCausal
def Q1 : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : MeasurableSpace Ω) (P : Ω → ℝ)
    (hP : @Measurable _ _ (eventuallyMeasurableSpace F (ae μ)) _ P),
    ∃ version : Ω → ℝ, Measurable[F] version ∧ P =ᶠ[ae μ] version

theorem wholePublicValue1 : Q1 := @BanditRL.OnlineLearning.completed_measurable_real_exists_version

#check wholePublicValue1
#print axioms wholePublicValue1
def Q2 : Prop := ∀ {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (S : Ω → Seed)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, @Measurable _ _ (eventuallyMeasurableSpace (F t) (ae μ)) _ (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1),
    ∃ policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
      (∀ t, Measurable (policy t)) ∧
      (∀ t q, policy t q ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ ω ∂μ, ∀ t, prediction t ω = policy t (S ω, fun i => Y i ω)

theorem wholePublicValue2 : Q2 := @BanditRL.OnlineLearning.completed_predictable_exists_bounded_history_policy

#check wholePublicValue2
#print axioms wholePublicValue2
def Q3 : Prop := ∀ {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ)
    (hP : @Measurable _ _ (eventuallyMeasurableSpace F (ae μ)) _ P),
    IndepFun P (Y t) μ

theorem wholePublicValue3 : Q3 := @BanditRL.OnlineLearning.completed_predictable_private_seed_independent

#check wholePublicValue3
#print axioms wholePublicValue3
def Q4 : Prop := ∀ {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, @Measurable _ _ (eventuallyMeasurableSpace (F t) (ae μ)) _ (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T

theorem wholePublicValue4 : Q4 := @BanditRL.OnlineLearning.completed_predictable_private_seed_expectedFixed_excess

#check wholePublicValue4
#print axioms wholePublicValue4
end NeutralCompletedCausal

#check BanditRL.OnlineLearning.completed_measurable_real_exists_version
#print axioms BanditRL.OnlineLearning.completed_measurable_real_exists_version
#check BanditRL.OnlineLearning.completed_predictable_exists_bounded_history_policy
#print axioms BanditRL.OnlineLearning.completed_predictable_exists_bounded_history_policy
#check BanditRL.OnlineLearning.completed_predictable_private_seed_independent
#print axioms BanditRL.OnlineLearning.completed_predictable_private_seed_independent
#check BanditRL.OnlineLearning.completed_predictable_private_seed_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.completed_predictable_private_seed_expectedFixed_excess
#check Tests.OnlineGuessingCompletedCausal.bad_completed_measurable
#print axioms Tests.OnlineGuessingCompletedCausal.bad_completed_measurable
#check Tests.OnlineGuessingCompletedCausal.bad_completed_but_not_ordinary_at_zero
#print axioms Tests.OnlineGuessingCompletedCausal.bad_completed_but_not_ordinary_at_zero
#check Tests.OnlineGuessingCompletedCausal.actual_completed_real_version
#print axioms Tests.OnlineGuessingCompletedCausal.actual_completed_real_version
#check Tests.OnlineGuessingCompletedCausal.actual_all_time_bounded_policy
#print axioms Tests.OnlineGuessingCompletedCausal.actual_all_time_bounded_policy
#check Tests.OnlineGuessingCompletedCausal.actual_current_independence
#print axioms Tests.OnlineGuessingCompletedCausal.actual_current_independence
#check Tests.OnlineGuessingCompletedCausal.actual_original_excess_identity
#print axioms Tests.OnlineGuessingCompletedCausal.actual_original_excess_identity
#check Tests.OnlineGuessingCompletedCausal.actual_nonzero_excess
#print axioms Tests.OnlineGuessingCompletedCausal.actual_nonzero_excess
#check Tests.OnlineGuessingCompletedCausal.actual_two_round_excess
#print axioms Tests.OnlineGuessingCompletedCausal.actual_two_round_excess
#check Tests.OnlineGuessingCompletedCausal.actual_empty_excess
#print axioms Tests.OnlineGuessingCompletedCausal.actual_empty_excess
#check Tests.OnlineGuessingCompletedCausal.actual_positive_target_variance
#print axioms Tests.OnlineGuessingCompletedCausal.actual_positive_target_variance
#check Tests.OnlineGuessingCompletedCausal.bad_still_not_everywhere_unit
#print axioms Tests.OnlineGuessingCompletedCausal.bad_still_not_everywhere_unit
#check BanditRL.OnlineLearning.ae_predictable_exists_bounded_history_policy
#print axioms BanditRL.OnlineLearning.ae_predictable_exists_bounded_history_policy
#check BanditRL.OnlineLearning.ae_predictable_private_seed_independent
#print axioms BanditRL.OnlineLearning.ae_predictable_private_seed_independent
#check BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess
#check BanditRL.OnlineLearning.privateSeedPastInformation
#print axioms BanditRL.OnlineLearning.privateSeedPastInformation
#check BanditRL.OnlineLearning.private_seed_past_independent
#print axioms BanditRL.OnlineLearning.private_seed_past_independent
#check BanditRL.OnlineLearning.predictable_private_seed_independent
#print axioms BanditRL.OnlineLearning.predictable_private_seed_independent
#check BanditRL.OnlineLearning.expectedFixedMinimum
#print axioms BanditRL.OnlineLearning.expectedFixedMinimum
#check BanditRL.OnlineLearning.expectedFixedRegret
#print axioms BanditRL.OnlineLearning.expectedFixedRegret
#check BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#print axioms BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#check BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition
#print axioms BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition
#check MeasurableSpace.measurable_mapNatBool
#print axioms MeasurableSpace.measurable_mapNatBool
#check MeasurableSpace.injective_mapNatBool
#print axioms MeasurableSpace.injective_mapNatBool
#check Measurable.measurableEmbedding
#print axioms Measurable.measurableEmbedding
#check MeasurableEmbedding.measurable_invFun
#print axioms MeasurableEmbedding.measurable_invFun
#check MeasurableEmbedding.leftInverse_invFun
#print axioms MeasurableEmbedding.leftInverse_invFun
#check MeasureTheory.ae_all_iff
#print axioms MeasureTheory.ae_all_iff
#check Tests.OnlineGuessingRandomizedIID.seededLaw
#print axioms Tests.OnlineGuessingRandomizedIID.seededLaw
#check Tests.OnlineGuessingRandomizedIID.seed
#print axioms Tests.OnlineGuessingRandomizedIID.seed
#check Tests.OnlineGuessingRandomizedIID.target
#print axioms Tests.OnlineGuessingRandomizedIID.target
#check Tests.OnlineGuessingRandomizedIID.seededLaw_probability
#print axioms Tests.OnlineGuessingRandomizedIID.seededLaw_probability
#check Tests.OnlineGuessingRandomizedIID.seed_measurable
#print axioms Tests.OnlineGuessingRandomizedIID.seed_measurable
#check Tests.OnlineGuessingRandomizedIID.target_measurable
#print axioms Tests.OnlineGuessingRandomizedIID.target_measurable
#check Tests.OnlineGuessingRandomizedIID.seed_has_coinLaw
#print axioms Tests.OnlineGuessingRandomizedIID.seed_has_coinLaw
#check Tests.OnlineGuessingRandomizedIID.target_has_coinLaw
#print axioms Tests.OnlineGuessingRandomizedIID.target_has_coinLaw
#check Tests.OnlineGuessingRandomizedIID.target_sameLaw
#print axioms Tests.OnlineGuessingRandomizedIID.target_sameLaw
#check Tests.OnlineGuessingRandomizedIID.target_support
#print axioms Tests.OnlineGuessingRandomizedIID.target_support
#check Tests.OnlineGuessingRandomizedIID.target_independent
#print axioms Tests.OnlineGuessingRandomizedIID.target_independent
#check Tests.OnlineGuessingRandomizedIID.seed_independent_whole_process
#print axioms Tests.OnlineGuessingRandomizedIID.seed_independent_whole_process
#check Tests.OnlineGuessingRandomizedIID.target_mean
#print axioms Tests.OnlineGuessingRandomizedIID.target_mean
#check Tests.OnlineGuessingRandomizedIID.target_variance
#print axioms Tests.OnlineGuessingRandomizedIID.target_variance
#check Tests.OnlineGuessingAECausal.badPrediction
#print axioms Tests.OnlineGuessingAECausal.badPrediction
#check Tests.OnlineGuessingAECausal.bad_eq_causal_ae
#print axioms Tests.OnlineGuessingAECausal.bad_eq_causal_ae
#check Tests.OnlineGuessingAECausal.causal_version_measurable
#print axioms Tests.OnlineGuessingAECausal.causal_version_measurable
#check Tests.OnlineGuessingAECausal.bad_ae_unit
#print axioms Tests.OnlineGuessingAECausal.bad_ae_unit
#check Tests.OnlineGuessingAECausal.bad_is_not_pointwise_predictable
#print axioms Tests.OnlineGuessingAECausal.bad_is_not_pointwise_predictable
#check Tests.OnlineGuessingAECausal.bad_is_not_everywhere_unit
#print axioms Tests.OnlineGuessingAECausal.bad_is_not_everywhere_unit
#check Tests.OnlineGuessingAECausal.actual_mean_square
#print axioms Tests.OnlineGuessingAECausal.actual_mean_square
