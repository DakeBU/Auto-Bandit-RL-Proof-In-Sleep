import BanditRLProof.OnlineLearningHistory
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory ProbabilityTheory

namespace BanditRL.OnlineLearning

noncomputable def expectedFixedMinimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def expectedFixedRegret {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    expectedFixedMinimum μ Y T

end BanditRL.OnlineLearning

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
