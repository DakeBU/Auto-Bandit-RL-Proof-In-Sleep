import Tests.OnlineGuessingIIDBenchmarkCanary
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
import Mathlib
import BanditRLProof.OnlineLearningHistory
import Mathlib.Order.ConditionallyCompleteLattice.Basic



open BanditRL.OnlineLearning
namespace DraftExpected
def Q001 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (u : ℝ),
    (∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) =
      (T : ℝ) * variance (Y 0) μ +
        (T : ℝ) * (u - ∫ ω, Y 0 ω ∂μ)^2

def Q002 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
        Set.Icc (0 : ℝ) 1) ((T : ℝ) * variance (Y 0) μ)

def Q003 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    expectedFixedMinimum μ Y T = (T : ℝ) * variance (Y 0) μ

def Q004 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, MemLp (prediction t) 2 μ)
    (hInd : ∀ t, IndepFun (prediction t) (Y t) μ) (T : ℕ),
    (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
      (T : ℝ) * variance (Y 0) μ =
        ∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ

def Q005 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t z ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    expectedFixedRegret μ Y (fun t ω => policy t (fun i => Y i ω)) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y (fun t ω => policy t (fun i => Y i ω)) T

def Q006 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ) (T : ℕ),
    expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T

def Q007 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      expectedFixedRegret μ Y (fun _ _ => ∫ ω, Y 0 ω ∂μ) T = 0

def Q008 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t z ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T),
    (∫ ω, ∑ t ∈ Finset.range T, (policy t (fun i => Y i ω) - Y t ω)^2 ∂μ) /
        (T : ℝ) - variance (Y 0) μ =
      expectedFixedRegret μ Y (fun t ω => policy t (fun i => Y i ω)) T / (T : ℝ)

end DraftExpected
#check BanditRL.OnlineLearning.expected_square_decomposition
#check BanditRL.OnlineLearning.independent_prediction_square
#check BanditRL.OnlineLearning.history_policy_independent
#check BanditRL.OnlineLearning.meanPredict_independent
#check BanditRL.OnlineLearning.meanPredict_measurable
#check BanditRL.OnlineLearning.meanPredict_mem
#check BanditRL.OnlineLearning.source_mean_optimal
#check BanditRL.OnlineLearning.iid_meanPredict_excess
#check BanditRL.OnlineLearning.normalized_excess
#check MeasureTheory.integral_finset_sum
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.integral_nonneg_of_ae
#check ae_all_iff
#check IsLeast.csInf_eq
#check MemLp.integrable_sq

open MeasureTheory ProbabilityTheory
namespace NeutralExpected
noncomputable def C2 (y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, y t) / T
noncomputable def C3 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 / 2 else C2 y t
noncomputable def C0 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def C1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    C0 μ Y T

def Q001 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (u : ℝ),
    (∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) =
      (T : ℝ) * variance (Y 0) μ +
        (T : ℝ) * (u - ∫ ω, Y 0 ω ∂μ)^2

def Q002 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
        Set.Icc (0 : ℝ) 1) ((T : ℝ) * variance (Y 0) μ)

def Q003 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    C0 μ Y T = (T : ℝ) * variance (Y 0) μ

def Q004 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, MemLp (prediction t) 2 μ)
    (hInd : ∀ t, IndepFun (prediction t) (Y t) μ) (T : ℕ),
    (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
      (T : ℝ) * variance (Y 0) μ =
        ∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ

def Q005 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t z ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    C1 μ Y (fun t ω => policy t (fun i => Y i ω)) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ C1 μ Y (fun t ω => policy t (fun i => Y i ω)) T

def Q006 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ) (T : ℕ),
    C1 μ Y (fun t ω => C3 (fun i => Y i ω) t) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (C3 (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ C1 μ Y (fun t ω => C3 (fun i => Y i ω) t) T

def Q007 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      C1 μ Y (fun _ _ => ∫ ω, Y 0 ω ∂μ) T = 0

def Q008 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t z ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T),
    (∫ ω, ∑ t ∈ Finset.range T, (policy t (fun i => Y i ω) - Y t ω)^2 ∂μ) /
        (T : ℝ) - variance (Y 0) μ =
      C1 μ Y (fun t ω => policy t (fun i => Y i ω)) T / (T : ℝ)

end NeutralExpected

universe u
example : DraftExpected.Q001.{u} = NeutralExpected.Q001.{u} := rfl
example : DraftExpected.Q002.{u} = NeutralExpected.Q002.{u} := rfl
example : DraftExpected.Q003.{u} = NeutralExpected.Q003.{u} := rfl
example : DraftExpected.Q004.{u} = NeutralExpected.Q004.{u} := rfl
example : DraftExpected.Q005.{u} = NeutralExpected.Q005.{u} := rfl
example : DraftExpected.Q006.{u} = NeutralExpected.Q006.{u} := rfl
example : DraftExpected.Q007.{u} = NeutralExpected.Q007.{u} := rfl
example : DraftExpected.Q008.{u} = NeutralExpected.Q008.{u} := rfl
example : @BanditRL.OnlineLearning.expectedFixedMinimum = @NeutralExpected.C0 := rfl
example : @BanditRL.OnlineLearning.expectedFixedRegret = @NeutralExpected.C1 := rfl
example : @BanditRL.OnlineLearning.empiricalMean = @NeutralExpected.C2 := rfl
example : @BanditRL.OnlineLearning.meanPredict = @NeutralExpected.C3 := rfl

namespace ActualTypeVerification
def propositionOf {P : Prop} (_ : P) : Prop := P
example : DraftExpected.Q001.{u} = propositionOf (@BanditRL.OnlineLearning.expected_fixed_prefix_decomposition.{u}) := by rfl
example : DraftExpected.Q002.{u} = propositionOf (@BanditRL.OnlineLearning.expected_fixed_prefix_minimum.{u}) := by rfl
example : DraftExpected.Q003.{u} = propositionOf (@BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance.{u}) := by rfl
example : DraftExpected.Q004.{u} = propositionOf (@BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition.{u}) := by rfl
example : DraftExpected.Q005.{u} = propositionOf (@BanditRL.OnlineLearning.history_policy_expectedFixed_excess.{u}) := by rfl
example : DraftExpected.Q006.{u} = propositionOf (@BanditRL.OnlineLearning.meanPredict_expectedFixed_excess.{u}) := by rfl
example : DraftExpected.Q007.{u} = propositionOf (@BanditRL.OnlineLearning.constant_mean_expectedFixed_excess_zero.{u}) := by rfl
example : DraftExpected.Q008.{u} = propositionOf (@BanditRL.OnlineLearning.history_policy_normalized_expectedFixed_excess.{u}) := by rfl
open Tests.OnlineGuessingIIDBenchmark

def C001 : Prop := ∀ᵐ x ∂coinLaw, x ∈ Set.Icc (0 : ℝ) 1
example : C001 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.coinLaw_support) := by rfl

def C002 : Prop := ∀ (f : ℝ → ℝ),
(∫ x, f x ∂coinLaw) = (f 0 + f 1) / 2
example : C002 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.coinLaw_integral) := by rfl

def C003 : Prop := ∀ (t : ℕ),
Measurable (observation t)
example : C003 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.observation_measurable) := by rfl

def C004 : Prop := ∀ (t : ℕ),
IdentDistrib (observation t) (fun x : ℝ => x) iidLaw coinLaw
example : C004 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.observation_has_coinLaw) := by rfl

def C005 : Prop := ∀ (t : ℕ),
IdentDistrib (observation t) (observation 0) iidLaw iidLaw
example : C005 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.observation_sameLaw) := by rfl

def C006 : Prop := ∀ (t : ℕ),
∀ᵐ ω ∂iidLaw, observation t ω ∈ Set.Icc (0 : ℝ) 1
example : C006 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.observation_support) := by rfl

def C007 : Prop := iIndepFun observation iidLaw
example : C007 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.observation_independent) := by rfl

def C008 : Prop := ∀ (t : ℕ),
(∫ ω, observation t ω ∂iidLaw) = 1 / 2
example : C008 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.observation_mean) := by rfl

def C009 : Prop := ∀ (t : ℕ),
variance (observation t) iidLaw = 1 / 4
example : C009 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.observation_variance) := by rfl

def C010 : Prop := ¬ (∀ t ω, observation t ω ∈ Set.Icc (0 : ℝ) 1)
example : C010 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.support_is_not_pointwise) := by rfl

def C011 : Prop := expectedFixedMinimum iidLaw observation 0 = 0
example : C011 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.empty_minimum) := by rfl

def C012 : Prop := expectedFixedMinimum iidLaw observation 2 = 1 / 2
example : C012 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.two_round_fixed_minimum) := by rfl

def C013 : Prop := IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range 2, (u - observation t ω)^2 ∂iidLaw) ''
      Set.Icc (0 : ℝ) 1) (1 / 2)
example : C013 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.actual_mean_attainment) := by rfl

def C014 : Prop := ∀ (T : ℕ),
0 ≤ expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T
example : C014 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.actual_meanPredict_nonnegative) := by rfl

def C015 : Prop := expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = 1 / 4
example : C015 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.meanPredict_two_round_excess) := by rfl

def C016 : Prop := ∀ (T : ℕ),
expectedFixedRegret iidLaw observation (fun _ _ => (1 / 2 : ℝ)) T = 0
example : C016 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.constant_known_mean_zero) := by rfl

def C017 : Prop := ∀ (t : ℕ),
Measurable (lastPolicy t)
example : C017 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.lastPolicy_measurable) := by rfl

def C018 : Prop := ∀ (t : ℕ) (z : (↑(Finset.range t) : Type) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1),
lastPolicy t z ∈ Set.Icc (0 : ℝ) 1
example : C018 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.lastPolicy_legal) := by rfl

def C019 : Prop := ¬ (∀ t z, lastPolicy t z ∈ Set.Icc (0 : ℝ) 1)
example : C019 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.lastPolicy_not_globally_bounded) := by rfl

def C020 : Prop := ∀ (t : ℕ),
IndepFun (fun ω => lastPolicy t (fun i => observation i ω)) (observation t) iidLaw
example : C020 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.actual_history_independent) := by rfl

def C021 : Prop := ∀ (T : ℕ),
0 ≤ expectedFixedRegret iidLaw observation (fun t ω => lastPolicy t (fun i => observation i ω)) T
example : C021 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.actual_history_nonnegative) := by rfl

def C022 : Prop := (∫ ω, ∑ t ∈ Finset.range 2,
      (lastPolicy t (fun i => observation i ω) - observation t ω)^2 ∂iidLaw) / 2 - 1 / 4 =
        expectedFixedRegret iidLaw observation (fun t ω => lastPolicy t (fun i => observation i ω)) 2 / 2
example : C022 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.actual_history_normalization) := by rfl

def C023 : Prop := ∀ (T : ℕ),
expectedFixedMinimum iidLaw (fun _ => observation 0) T = (T : ℝ) / 4
example : C023 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.repeated_target_fixed_minimum) := by rfl

def C024 : Prop := (∫ ω, ∑ t ∈ Finset.range 2, ((2 : ℝ) - observation t ω)^2 ∂iidLaw) = 5
example : C024 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.infeasible_fixed_comparator_two) := by rfl

def C025 : Prop := (∫ ω, (observation 0 ω - observation 1 ω)^2 ∂iidLaw) = 1 / 2
example : C025 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.independent_difference_square) := by rfl

def C026 : Prop := (∫ ω, hindsightMinimum ω 2 ∂iidLaw) = 1 / 4
example : C026 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.hindsight_minimum_two) := by rfl

def C027 : Prop := (∫ ω, hindsightMinimum ω 2 ∂iidLaw) < expectedFixedMinimum iidLaw observation 2
example : C027 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.min_and_expectation_do_not_commute) := by rfl

def C028 : Prop := expectedFixedRegret iidLaw observation observation 2 = -1 / 2
example : C028 = propositionOf (@Tests.OnlineGuessingIIDBenchmark.current_target_cheating_negative) := by rfl

def coinLawFixture : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1
example : @coinLawFixture = @Tests.OnlineGuessingIIDBenchmark.coinLaw := by rfl

def iidLawFixture : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => coinLaw)
example : @iidLawFixture = @Tests.OnlineGuessingIIDBenchmark.iidLaw := by rfl

def observationFixture (t : ℕ) (ω : ℕ → ℝ) : ℝ := ω t
example : @observationFixture = @Tests.OnlineGuessingIIDBenchmark.observation := by rfl

def lastPolicyFixture (t : ℕ) (z : (↑(Finset.range t) : Type) → ℝ) : ℝ :=
  if h : t = 0 then 1 / 2 else
    z ⟨t - 1, Finset.mem_range.mpr (Nat.sub_lt (Nat.pos_of_ne_zero h) (by omega))⟩
example : @lastPolicyFixture = @Tests.OnlineGuessingIIDBenchmark.lastPolicy := by rfl

def hindsightMinimumFixture (ω : ℕ → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - ω t)^2) '' Set.Icc (0 : ℝ) 1)
example : @hindsightMinimumFixture = @Tests.OnlineGuessingIIDBenchmark.hindsightMinimum := by rfl
end ActualTypeVerification
