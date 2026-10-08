import Tests.OnlineGuessingKernelCausalCanary
open MeasureTheory ProbabilityTheory unitInterval BanditRL.OnlineLearning
namespace NeutralKernelCausal
def Q1 : Prop := ∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)],
    ∃ f : KernelDecisionSampler,
      (∀ t, Measurable (Function.uncurry (f t))) ∧
      ∀ t h, (volume : Measure I).map (f t h) = κ t h

theorem wholePublicValue1 : Q1 := @BanditRL.OnlineLearning.kernel_sampler_family_exists

#check wholePublicValue1
#print axioms wholePublicValue1
def Q2 : Prop := ∀ (f : KernelDecisionSampler) (hf : ∀ t, Measurable (Function.uncurry (f t))),
    (∀ t, Measurable (kernelCausalPolicy f t)) ∧
    (∀ t (u : ℕ → I) (y : ℕ → ℝ) (i : Fin t),
      kernelGeneratedActions f t (fun j => u j) (fun j => y j) i =
        kernelGeneratedPrediction f (i : ℕ) (u, y)) ∧
    ∀ t (ω ω' : (ℕ → I) × (ℕ → ℝ)),
      (∀ i, i ≤ t → ω.1 i = ω'.1 i) →
      (∀ i, i < t → ω.2 i = ω'.2 i) →
      kernelGeneratedPrediction f t ω = kernelGeneratedPrediction f t ω'

theorem wholePublicValue2 : Q2 := @BanditRL.OnlineLearning.kernel_sampler_causal_process

#check wholePublicValue2
#print axioms wholePublicValue2
def Q3 : Prop := ∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)]
    (f : KernelDecisionSampler) (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hκ : ∀ t h, (volume : Measure I).map (f t h) = κ t h)
    (ν : ProbabilityMeasure (ℕ → ℝ)) (t : ℕ),
    (kernelGameLaw ν).map (fun ω =>
      (kernelGeneratedHistory f t ω, kernelGeneratedPrediction f t ω)) =
      (kernelGameLaw ν).map (kernelGeneratedHistory f t) ⊗ₘ κ t

theorem wholePublicValue3 : Q3 := @BanditRL.OnlineLearning.kernel_sampler_joint_law

#check wholePublicValue3
#print axioms wholePublicValue3
def Q4 : Prop := ∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)]
    (f : KernelDecisionSampler) (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hκ : ∀ t h, (volume : Measure I).map (f t h) = κ t h)
    (ν : ProbabilityMeasure (ℕ → ℝ)) (t : ℕ),
    condDistrib (kernelGeneratedPrediction f t) (kernelGeneratedHistory f t) (kernelGameLaw ν)
      =ᵐ[(kernelGameLaw ν).map (kernelGeneratedHistory f t)] κ t

theorem wholePublicValue4 : Q4 := @BanditRL.OnlineLearning.kernel_sampler_conditional_law

#check wholePublicValue4
#print axioms wholePublicValue4
def Q5 : Prop := ∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)],
    ∃ f : KernelDecisionSampler,
      (∀ t, Measurable (Function.uncurry (f t))) ∧
      (∀ t h, (volume : Measure I).map (f t h) = κ t h) ∧
      (∀ t, Measurable (kernelCausalPolicy f t)) ∧
      (∀ t (u : ℕ → I) (y : ℕ → ℝ) (i : Fin t),
        kernelGeneratedActions f t (fun j => u j) (fun j => y j) i =
          kernelGeneratedPrediction f (i : ℕ) (u, y)) ∧
      (∀ t (ω ω' : (ℕ → I) × (ℕ → ℝ)),
        (∀ i, i ≤ t → ω.1 i = ω'.1 i) →
        (∀ i, i < t → ω.2 i = ω'.2 i) →
        kernelGeneratedPrediction f t ω = kernelGeneratedPrediction f t ω') ∧
      ∀ ν : ProbabilityMeasure (ℕ → ℝ),
        (∀ t, (kernelGameLaw ν).map (fun ω =>
          (kernelGeneratedHistory f t ω, kernelGeneratedPrediction f t ω)) =
          (kernelGameLaw ν).map (kernelGeneratedHistory f t) ⊗ₘ κ t) ∧
        (∀ t, condDistrib (kernelGeneratedPrediction f t) (kernelGeneratedHistory f t)
          (kernelGameLaw ν) =ᵐ[(kernelGameLaw ν).map (kernelGeneratedHistory f t)] κ t) ∧
        (iIndepFun (fun t (y : ℕ → ℝ) => y t) (ν : Measure (ℕ → ℝ)) →
          (∀ t, IdentDistrib (fun y : ℕ → ℝ => y t) (fun y : ℕ → ℝ => y 0)
            (ν : Measure (ℕ → ℝ)) (ν : Measure (ℕ → ℝ))) →
          (∀ t, ∀ᵐ y ∂(ν : Measure (ℕ → ℝ)), y t ∈ Set.Icc (0 : ℝ) 1) →
          ∀ T : ℕ,
            expectedFixedRegret (kernelGameLaw ν) (fun t ω => ω.2 t)
              (fun t ω => (kernelGeneratedPrediction f t ω : ℝ)) T =
              (∑ t ∈ Finset.range T, ∫ ω,
                ((kernelGeneratedPrediction f t ω : ℝ) -
                  ∫ ω, ω.2 0 ∂(kernelGameLaw ν))^2 ∂(kernelGameLaw ν)) ∧
            0 ≤ expectedFixedRegret (kernelGameLaw ν) (fun t ω => ω.2 t)
              (fun t ω => (kernelGeneratedPrediction f t ω : ℝ)) T)

theorem wholePublicValue5 : Q5 := @BanditRL.OnlineLearning.causal_kernel_realization_and_expectedFixed_excess

#check wholePublicValue5
#print axioms wholePublicValue5
end NeutralKernelCausal

#check BanditRL.OnlineLearning.kernel_sampler_family_exists
#print axioms BanditRL.OnlineLearning.kernel_sampler_family_exists
#check BanditRL.OnlineLearning.kernel_sampler_causal_process
#print axioms BanditRL.OnlineLearning.kernel_sampler_causal_process
#check BanditRL.OnlineLearning.kernel_sampler_joint_law
#print axioms BanditRL.OnlineLearning.kernel_sampler_joint_law
#check BanditRL.OnlineLearning.kernel_sampler_conditional_law
#print axioms BanditRL.OnlineLearning.kernel_sampler_conditional_law
#check BanditRL.OnlineLearning.causal_kernel_realization_and_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.causal_kernel_realization_and_expectedFixed_excess
#check Tests.OnlineGuessingKernelCausal.switchSet_measurable
#print axioms Tests.OnlineGuessingKernelCausal.switchSet_measurable
#check Tests.OnlineGuessingKernelCausal.public_family_realizes
#print axioms Tests.OnlineGuessingKernelCausal.public_family_realizes
#check Tests.OnlineGuessingKernelCausal.public_causal_process
#print axioms Tests.OnlineGuessingKernelCausal.public_causal_process
#check Tests.OnlineGuessingKernelCausal.public_joint_law
#print axioms Tests.OnlineGuessingKernelCausal.public_joint_law
#check Tests.OnlineGuessingKernelCausal.public_conditional_law
#print axioms Tests.OnlineGuessingKernelCausal.public_conditional_law
#check Tests.OnlineGuessingKernelCausal.actual_process_excess
#print axioms Tests.OnlineGuessingKernelCausal.actual_process_excess
#check Tests.OnlineGuessingKernelCausal.history_feedback_distribution
#print axioms Tests.OnlineGuessingKernelCausal.history_feedback_distribution
#check Tests.OnlineGuessingKernelCausal.every_history_stochastic
#print axioms Tests.OnlineGuessingKernelCausal.every_history_stochastic
#check Tests.OnlineGuessingKernelCausal.actual_prediction_binary
#print axioms Tests.OnlineGuessingKernelCausal.actual_prediction_binary
#check Tests.OnlineGuessingKernelCausal.target_positive_variance
#print axioms Tests.OnlineGuessingKernelCausal.target_positive_variance
#check Tests.OnlineGuessingKernelCausal.every_horizon_excess
#print axioms Tests.OnlineGuessingKernelCausal.every_horizon_excess
#check Tests.OnlineGuessingKernelCausal.zero_horizon_excess
#print axioms Tests.OnlineGuessingKernelCausal.zero_horizon_excess
#check Tests.OnlineGuessingKernelCausal.positive_two_round_excess
#print axioms Tests.OnlineGuessingKernelCausal.positive_two_round_excess
#check BanditRL.OnlineLearning.KernelDecisionHistory
#print axioms BanditRL.OnlineLearning.KernelDecisionHistory
#check BanditRL.OnlineLearning.KernelDecisionSampler
#print axioms BanditRL.OnlineLearning.KernelDecisionSampler
#check BanditRL.OnlineLearning.kernelGeneratedActions
#print axioms BanditRL.OnlineLearning.kernelGeneratedActions
#check BanditRL.OnlineLearning.kernelCausalPolicy
#print axioms BanditRL.OnlineLearning.kernelCausalPolicy
#check BanditRL.OnlineLearning.kernelGeneratedHistory
#print axioms BanditRL.OnlineLearning.kernelGeneratedHistory
#check BanditRL.OnlineLearning.kernelGeneratedPrediction
#print axioms BanditRL.OnlineLearning.kernelGeneratedPrediction
#check BanditRL.OnlineLearning.kernelUniformTapeLaw
#print axioms BanditRL.OnlineLearning.kernelUniformTapeLaw
#check BanditRL.OnlineLearning.kernelGameLaw
#print axioms BanditRL.OnlineLearning.kernelGameLaw
#check Tests.OnlineGuessingKernelCausal.lowLaw
#print axioms Tests.OnlineGuessingKernelCausal.lowLaw
#check Tests.OnlineGuessingKernelCausal.highLaw
#print axioms Tests.OnlineGuessingKernelCausal.highLaw
#check Tests.OnlineGuessingKernelCausal.lowLaw_probability
#print axioms Tests.OnlineGuessingKernelCausal.lowLaw_probability
#check Tests.OnlineGuessingKernelCausal.highLaw_probability
#print axioms Tests.OnlineGuessingKernelCausal.highLaw_probability
#check Tests.OnlineGuessingKernelCausal.switchSet
#print axioms Tests.OnlineGuessingKernelCausal.switchSet
#check Tests.OnlineGuessingKernelCausal.decisionKernel
#print axioms Tests.OnlineGuessingKernelCausal.decisionKernel
#check Tests.OnlineGuessingKernelCausal.decisionKernel_markov
#print axioms Tests.OnlineGuessingKernelCausal.decisionKernel_markov
#check Tests.OnlineGuessingKernelCausal.oneHistory
#print axioms Tests.OnlineGuessingKernelCausal.oneHistory
#check Tests.OnlineGuessingKernelCausal.selectedSampler
#print axioms Tests.OnlineGuessingKernelCausal.selectedSampler
#check Tests.OnlineGuessingKernelCausal.observationLaw
#print axioms Tests.OnlineGuessingKernelCausal.observationLaw
#check Tests.OnlineGuessingKernelCausal.prediction
#print axioms Tests.OnlineGuessingKernelCausal.prediction
#check Tests.OnlineGuessingKernelCausal.target
#print axioms Tests.OnlineGuessingKernelCausal.target
#check Tests.OnlineGuessingKernelCausal.gameLaw
#print axioms Tests.OnlineGuessingKernelCausal.gameLaw
#check BanditRL.OnlineLearning.independent_private_seed_pair
#print axioms BanditRL.OnlineLearning.independent_private_seed_pair
#check BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
#check BanditRL.OnlineLearning.expectedFixedMinimum
#print axioms BanditRL.OnlineLearning.expectedFixedMinimum
#check BanditRL.OnlineLearning.expectedFixedRegret
#print axioms BanditRL.OnlineLearning.expectedFixedRegret
#check BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#print axioms BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#check BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition
#print axioms BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition
#check ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval
#print axioms ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval
#check ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
#print axioms ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
#check ProbabilityTheory.iIndepFun_infinitePi
#print axioms ProbabilityTheory.iIndepFun_infinitePi
#check ProbabilityTheory.indepFun_prod
#print axioms ProbabilityTheory.indepFun_prod
#check ProbabilityTheory.iIndepFun.indepFun_finset
#print axioms ProbabilityTheory.iIndepFun.indepFun_finset
#check MeasureTheory.Measure.infinitePi_map_eval
#print axioms MeasureTheory.Measure.infinitePi_map_eval
#check MeasureTheory.Measure.compProd_apply
#print axioms MeasureTheory.Measure.compProd_apply
