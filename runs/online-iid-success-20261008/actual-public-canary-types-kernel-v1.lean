import Tests.OnlineGuessingIIDSuccessCanary
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Filter Asymptotics
universe u v
namespace BanditRL.OnlineLearning

def S001 : Prop := ∀ (total : ℕ → ℝ) (c : ℝ),
    (fun T => total T - (T : ℝ) * c) =o[atTop] (fun T : ℕ => (T : ℝ)) ↔
      Tendsto (fun T => total T / (T : ℝ) - c) atTop (nhds (0 : ℝ))

def S002 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t s z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t (s, z) ∈ Set.Icc (0 : ℝ) 1),
    let prediction := fun t ω => policy t (S ω, fun i => Y i ω)
    (∀ T, 0 ≤ expectedFixedRegret μ Y prediction T) ∧
      ((fun T => expectedFixedRegret μ Y prediction T) =o[atTop]
          (fun T : ℕ => (T : ℝ)) ↔
        Tendsto (fun T => (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) / (T : ℝ) - variance (Y 0) μ) atTop (nhds (0 : ℝ))) ∧
      (Tendsto (fun T => (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) / (T : ℝ) - variance (Y 0) μ) atTop (nhds (0 : ℝ)) ↔
        Tendsto (fun T => (∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) / (T : ℝ)) atTop (nhds (0 : ℝ)))

def S003 : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T),
    expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T ≤ 4 + 4 * Real.log T

def S004 : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ),
    Tendsto (fun T => expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (fun T => expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T) =o[atTop]
        (fun T : ℕ => (T : ℝ))

end BanditRL.OnlineLearning
open MeasureTheory ProbabilityTheory Filter Asymptotics
namespace NeutralLimit

noncomputable def C0 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def C1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    C0 μ Y T

noncomputable def C2 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then (1 : ℝ) / 2 else (∑ i ∈ Finset.range t, y i) / (t : ℝ)

def Q001 : Prop := ∀ (total : ℕ → ℝ) (c : ℝ),
    (fun T => total T - (T : ℝ) * c) =o[atTop] (fun T : ℕ => (T : ℝ)) ↔
      Tendsto (fun T => total T / (T : ℝ) - c) atTop (nhds (0 : ℝ))

def Q002 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t s z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t (s, z) ∈ Set.Icc (0 : ℝ) 1),
    let prediction := fun t ω => policy t (S ω, fun i => Y i ω)
    (∀ T, 0 ≤ C1 μ Y prediction T) ∧
      ((fun T => C1 μ Y prediction T) =o[atTop]
          (fun T : ℕ => (T : ℝ)) ↔
        Tendsto (fun T => (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) / (T : ℝ) - variance (Y 0) μ) atTop (nhds (0 : ℝ))) ∧
      (Tendsto (fun T => (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) / (T : ℝ) - variance (Y 0) μ) atTop (nhds (0 : ℝ)) ↔
        Tendsto (fun T => (∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) / (T : ℝ)) atTop (nhds (0 : ℝ)))

def Q003 : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T),
    C1 μ Y (fun t ω => C2 (fun i => Y i ω) t) T ≤ 4 + 4 * Real.log T

def Q004 : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (hind : iIndepFun Y μ),
    Tendsto (fun T => C1 μ Y (fun t ω => C2 (fun i => Y i ω) t) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (fun T => C1 μ Y (fun t ω => C2 (fun i => Y i ω) t) T) =o[atTop]
        (fun T : ℕ => (T : ℝ))

end NeutralLimit

open BanditRL.OnlineLearning NeutralLimit
example : S001 = Q001 := rfl
example : S001 := @BanditRL.OnlineLearning.centered_total_sublinear_iff_average
example : S002.{u, v} = Q002.{u, v} := rfl
example : S002.{u, v} := @BanditRL.OnlineLearning.randomized_history_policy_success_iff.{u, v}
example : S003.{u} = Q003.{u} := rfl
example : S003.{u} := @BanditRL.OnlineLearning.meanPredict_expectedFixed_upper.{u}
example : S004.{u} = Q004.{u} := rfl
example : S004.{u} := @BanditRL.OnlineLearning.meanPredict_iid_success.{u}
example : @C0.{u} = @expectedFixedMinimum.{u} := rfl
example : @C1.{u} = @expectedFixedRegret.{u} := rfl
example : C2 = meanPredict := rfl
#check BanditRL.OnlineLearning.centered_total_sublinear_iff_average
#print axioms BanditRL.OnlineLearning.centered_total_sublinear_iff_average
#check BanditRL.OnlineLearning.randomized_history_policy_success_iff
#print axioms BanditRL.OnlineLearning.randomized_history_policy_success_iff
#check BanditRL.OnlineLearning.meanPredict_expectedFixed_upper
#print axioms BanditRL.OnlineLearning.meanPredict_expectedFixed_upper
#check BanditRL.OnlineLearning.meanPredict_iid_success
#print axioms BanditRL.OnlineLearning.meanPredict_iid_success
#check Tests.OnlineGuessingIIDSuccess.actual_meanPredict_success
#print axioms Tests.OnlineGuessingIIDSuccess.actual_meanPredict_success
#check Tests.OnlineGuessingIIDSuccess.actual_meanPredict_upper
#print axioms Tests.OnlineGuessingIIDSuccess.actual_meanPredict_upper
#check Tests.OnlineGuessingIIDSuccess.actual_meanPredict_two_round_positive
#print axioms Tests.OnlineGuessingIIDSuccess.actual_meanPredict_two_round_positive
#check Tests.OnlineGuessingIIDSuccess.actual_positive_variance
#print axioms Tests.OnlineGuessingIIDSuccess.actual_positive_variance
#check Tests.OnlineGuessingIIDSuccess.persistentPolicy
#print axioms Tests.OnlineGuessingIIDSuccess.persistentPolicy
#check Tests.OnlineGuessingIIDSuccess.persistentPolicy_measurable
#print axioms Tests.OnlineGuessingIIDSuccess.persistentPolicy_measurable
#check Tests.OnlineGuessingIIDSuccess.persistentPolicy_legal
#print axioms Tests.OnlineGuessingIIDSuccess.persistentPolicy_legal
#check Tests.OnlineGuessingIIDSuccess.persistentPrediction
#print axioms Tests.OnlineGuessingIIDSuccess.persistentPrediction
#check Tests.OnlineGuessingIIDSuccess.persistent_excess
#print axioms Tests.OnlineGuessingIIDSuccess.persistent_excess
#check Tests.OnlineGuessingIIDSuccess.persistent_normalized_limit
#print axioms Tests.OnlineGuessingIIDSuccess.persistent_normalized_limit
#check Tests.OnlineGuessingIIDSuccess.persistent_not_sublinear
#print axioms Tests.OnlineGuessingIIDSuccess.persistent_not_sublinear
#check Tests.OnlineGuessingIIDSuccess.persistent_policy_not_successful
#print axioms Tests.OnlineGuessingIIDSuccess.persistent_policy_not_successful
#check Tests.OnlineGuessingIIDSuccess.zero_horizon_difference
#print axioms Tests.OnlineGuessingIIDSuccess.zero_horizon_difference
#check Tests.OnlineGuessingIIDSuccess.nonzero_initial_total_sublinear
#print axioms Tests.OnlineGuessingIIDSuccess.nonzero_initial_total_sublinear
#check Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_upper
#print axioms Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_upper
#check Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_negative_two
#print axioms Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_negative_two
#check BanditRL.OnlineLearning.expectedFixedMinimum
#print axioms BanditRL.OnlineLearning.expectedFixedMinimum
#check BanditRL.OnlineLearning.expectedFixedRegret
#print axioms BanditRL.OnlineLearning.expectedFixedRegret
#check BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#print axioms BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#check BanditRL.OnlineLearning.expected_fixed_prefix_decomposition
#print axioms BanditRL.OnlineLearning.expected_fixed_prefix_decomposition
#check BanditRL.OnlineLearning.meanPredict_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.meanPredict_expectedFixed_excess
#check BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
#check BanditRL.OnlineLearning.theorem_1_3
#print axioms BanditRL.OnlineLearning.theorem_1_3
#check BanditRL.OnlineLearning.empiricalMean_minimizes
#print axioms BanditRL.OnlineLearning.empiricalMean_minimizes
#check BanditRL.OnlineLearning.meanPredict
#print axioms BanditRL.OnlineLearning.meanPredict
#check BanditRL.OnlineLearning.empiricalMean
#print axioms BanditRL.OnlineLearning.empiricalMean
#check Tests.OnlineGuessingIIDBenchmark.coinLaw
#print axioms Tests.OnlineGuessingIIDBenchmark.coinLaw
#check Tests.OnlineGuessingIIDBenchmark.iidLaw
#print axioms Tests.OnlineGuessingIIDBenchmark.iidLaw
#check Tests.OnlineGuessingIIDBenchmark.observation
#print axioms Tests.OnlineGuessingIIDBenchmark.observation
#check Tests.OnlineGuessingIIDBenchmark.iidLaw_probability
#print axioms Tests.OnlineGuessingIIDBenchmark.iidLaw_probability
#check Tests.OnlineGuessingIIDBenchmark.observation_independent
#print axioms Tests.OnlineGuessingIIDBenchmark.observation_independent
#check Tests.OnlineGuessingIIDBenchmark.observation_support
#print axioms Tests.OnlineGuessingIIDBenchmark.observation_support
#check Tests.OnlineGuessingIIDBenchmark.observation_sameLaw
#print axioms Tests.OnlineGuessingIIDBenchmark.observation_sameLaw
#check Tests.OnlineGuessingIIDBenchmark.meanPredict_two_round_excess
#print axioms Tests.OnlineGuessingIIDBenchmark.meanPredict_two_round_excess
#check Tests.OnlineGuessingRandomizedIID.seededLaw
#print axioms Tests.OnlineGuessingRandomizedIID.seededLaw
#check Tests.OnlineGuessingRandomizedIID.seed
#print axioms Tests.OnlineGuessingRandomizedIID.seed
#check Tests.OnlineGuessingRandomizedIID.target
#print axioms Tests.OnlineGuessingRandomizedIID.target
#check Tests.OnlineGuessingRandomizedIID.seedBit
#print axioms Tests.OnlineGuessingRandomizedIID.seedBit
#check Tests.OnlineGuessingRandomizedIID.seededLaw_probability
#print axioms Tests.OnlineGuessingRandomizedIID.seededLaw_probability
#check Tests.OnlineGuessingRandomizedIID.seed_independent_whole_process
#print axioms Tests.OnlineGuessingRandomizedIID.seed_independent_whole_process
#check Tests.OnlineGuessingRandomizedIID.target_independent
#print axioms Tests.OnlineGuessingRandomizedIID.target_independent
