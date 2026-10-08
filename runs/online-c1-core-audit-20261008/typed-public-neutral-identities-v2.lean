import BanditRLProof.OnlineLearningHistory
import BanditRLProof.OnlineLearningFoundations
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory
universe u

namespace NeutralCoreAudit
def D01 (y : ℕ → ℝ) (T : ℕ) : ℝ := (∑ i ∈ Finset.range T, y i) / (T : ℝ)
def D02 (y : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 1/2 else D01 y t

def Q001 {X : Type u} (V : Set X) (loss : ℕ → X → ℝ) (leader : ℕ → X) (T : ℕ) (hmem : ∀ n, 0 < n → n ≤ T → leader n ∈ V) (hmin : ∀ n, 0 < n → n ≤ T → ∀ u ∈ V, (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u)  : Prop :=
  (∑ t ∈ Finset.range T, loss t (leader (t + 1))) ≤ ∑ t ∈ Finset.range T, loss t (leader T)

def Q002 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (u : ℝ)  : Prop :=
  (∫ ω, (u - Y ω)^2 ∂μ) = variance Y μ + (u - ∫ ω, Y ω ∂μ)^2

def Q003 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (P Y : Ω → ℝ) (hP : MemLp P 2 μ) (hY : MemLp Y 2 μ) (h : IndepFun P Y μ)  : Prop :=
  (∫ ω, (P ω - Y ω)^2 ∂μ) = (∫ ω, (P ω - ∫ ω, Y ω ∂μ)^2 ∂μ) + variance Y μ

def Q004 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ)  : Prop :=
  IndepFun (fun ω => D02 (fun i => Y i ω) t) (Y t) μ

def Q005 {Ω : Type u} [MeasurableSpace Ω] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (t : ℕ)  : Prop :=
  Measurable (fun ω => D02 (fun i => Y i ω) t)

def Q006 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ)  : Prop :=
  MemLp (fun ω => D02 (fun i => Y i ω) t) 2 μ

def Q007 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)  : Prop :=
  (∫ ω, ∑ t ∈ Finset.range T, (D02 (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ = ∑ t ∈ Finset.range T, ∫ ω, (D02 (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ

def Q008 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)  : Prop :=
  0 ≤ (∫ ω, ∑ t ∈ Finset.range T, (D02 (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ

def Q009 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y) (hb : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1)  : Prop :=
  (∫ ω, Y ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧ (∫ ω, ((∫ ω, Y ω ∂μ) - Y ω)^2 ∂μ) = variance Y μ ∧ ∀ u : ℝ, variance Y μ ≤ ∫ ω, (u - Y ω)^2 ∂μ

def Q010 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy)  : Prop :=
  IndepFun (fun ω => policy (fun i => Y i ω)) (Y t) μ

def Q011 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy) (hpb : ∀ z, policy z ∈ Set.Icc (0 : ℝ) 1)  : Prop :=
  variance (Y t) μ ≤ ∫ ω, (policy (fun i => Y i ω) - Y t ω)^2 ∂μ

def Q012 (total variance : ℝ) (T : ℕ) (hT : 0 < T)  : Prop :=
  total / T - variance = (total - T * variance) / T

end NeutralCoreAudit

open BanditRL.OnlineLearning
namespace PublicCoreAudit
def P001 {X : Type u} (V : Set X) (loss : ℕ → X → ℝ) (leader : ℕ → X) (T : ℕ) (hmem : ∀ n, 0 < n → n ≤ T → leader n ∈ V) (hmin : ∀ n, 0 < n → n ≤ T → ∀ u ∈ V, (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u)  : Prop :=  (∑ t ∈ Finset.range T, loss t (leader (t + 1))) ≤ ∑ t ∈ Finset.range T, loss t (leader T)
example : @P001 = @NeutralCoreAudit.Q001 := rfl
example {X : Type u} (V : Set X) (loss : ℕ → X → ℝ) (leader : ℕ → X) (T : ℕ) (hmem : ∀ n, 0 < n → n ≤ T → leader n ∈ V) (hmin : ∀ n, 0 < n → n ≤ T → ∀ u ∈ V, (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u) : (∑ t ∈ Finset.range T, loss t (leader (t + 1))) ≤ ∑ t ∈ Finset.range T, loss t (leader T) := by
  exact BanditRL.OnlineLearning.lemma_1_2 V loss leader T hmem hmin

#check BanditRL.OnlineLearning.lemma_1_2
#print axioms BanditRL.OnlineLearning.lemma_1_2
def P002 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (u : ℝ)  : Prop :=  (∫ ω, (u - Y ω)^2 ∂μ) = variance Y μ + (u - ∫ ω, Y ω ∂μ)^2
example : @P002 = @NeutralCoreAudit.Q002 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (u : ℝ) : (∫ ω, (u - Y ω)^2 ∂μ) = variance Y μ + (u - ∫ ω, Y ω ∂μ)^2 := by
  exact BanditRL.OnlineLearning.expected_square_decomposition μ Y hY u

#check BanditRL.OnlineLearning.expected_square_decomposition
#print axioms BanditRL.OnlineLearning.expected_square_decomposition
def P003 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (P Y : Ω → ℝ) (hP : MemLp P 2 μ) (hY : MemLp Y 2 μ) (h : IndepFun P Y μ)  : Prop :=  (∫ ω, (P ω - Y ω)^2 ∂μ) = (∫ ω, (P ω - ∫ ω, Y ω ∂μ)^2 ∂μ) + variance Y μ
example : @P003 = @NeutralCoreAudit.Q003 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (P Y : Ω → ℝ) (hP : MemLp P 2 μ) (hY : MemLp Y 2 μ) (h : IndepFun P Y μ) : (∫ ω, (P ω - Y ω)^2 ∂μ) = (∫ ω, (P ω - ∫ ω, Y ω ∂μ)^2 ∂μ) + variance Y μ := by
  exact BanditRL.OnlineLearning.independent_prediction_square μ P Y hP hY h

#check BanditRL.OnlineLearning.independent_prediction_square
#print axioms BanditRL.OnlineLearning.independent_prediction_square
def P004 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ)  : Prop :=  IndepFun (fun ω => meanPredict (fun i => Y i ω) t) (Y t) μ
example : @P004 = @NeutralCoreAudit.Q004 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ) : IndepFun (fun ω => meanPredict (fun i => Y i ω) t) (Y t) μ := by
  exact BanditRL.OnlineLearning.meanPredict_independent μ Y hY hind t

#check BanditRL.OnlineLearning.meanPredict_independent
#print axioms BanditRL.OnlineLearning.meanPredict_independent
def P005 {Ω : Type u} [MeasurableSpace Ω] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (t : ℕ)  : Prop :=  Measurable (fun ω => meanPredict (fun i => Y i ω) t)
example : @P005 = @NeutralCoreAudit.Q005 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (t : ℕ) : Measurable (fun ω => meanPredict (fun i => Y i ω) t) := by
  exact BanditRL.OnlineLearning.meanPredict_measurable Y hY t

#check BanditRL.OnlineLearning.meanPredict_measurable
#print axioms BanditRL.OnlineLearning.meanPredict_measurable
def P006 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ)  : Prop :=  MemLp (fun ω => meanPredict (fun i => Y i ω) t) 2 μ
example : @P006 = @NeutralCoreAudit.Q006 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) : MemLp (fun ω => meanPredict (fun i => Y i ω) t) 2 μ := by
  exact BanditRL.OnlineLearning.meanPredict_memLp μ Y hY hb t

#check BanditRL.OnlineLearning.meanPredict_memLp
#print axioms BanditRL.OnlineLearning.meanPredict_memLp
def P007 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)  : Prop :=  (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ = ∑ t ∈ Finset.range T, ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ
example : @P007 = @NeutralCoreAudit.Q007 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) : (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ = ∑ t ∈ Finset.range T, ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
  exact BanditRL.OnlineLearning.iid_meanPredict_excess μ Y hY hind hlaw hb T

#check BanditRL.OnlineLearning.iid_meanPredict_excess
#print axioms BanditRL.OnlineLearning.iid_meanPredict_excess
def P008 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)  : Prop :=  0 ≤ (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ
example : @P008 = @NeutralCoreAudit.Q008 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) : 0 ≤ (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ := by
  exact BanditRL.OnlineLearning.iid_meanPredict_excess_nonneg μ Y hY hind hlaw hb T

#check BanditRL.OnlineLearning.iid_meanPredict_excess_nonneg
#print axioms BanditRL.OnlineLearning.iid_meanPredict_excess_nonneg
def P009 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y) (hb : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1)  : Prop :=  (∫ ω, Y ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧ (∫ ω, ((∫ ω, Y ω ∂μ) - Y ω)^2 ∂μ) = variance Y μ ∧ ∀ u : ℝ, variance Y μ ≤ ∫ ω, (u - Y ω)^2 ∂μ
example : @P009 = @NeutralCoreAudit.Q009 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y) (hb : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1) : (∫ ω, Y ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧ (∫ ω, ((∫ ω, Y ω ∂μ) - Y ω)^2 ∂μ) = variance Y μ ∧ ∀ u : ℝ, variance Y μ ≤ ∫ ω, (u - Y ω)^2 ∂μ := by
  exact BanditRL.OnlineLearning.source_mean_optimal μ Y hY hb

#check BanditRL.OnlineLearning.source_mean_optimal
#print axioms BanditRL.OnlineLearning.source_mean_optimal
def P010 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy)  : Prop :=  IndepFun (fun ω => policy (fun i => Y i ω)) (Y t) μ
example : @P010 = @NeutralCoreAudit.Q010 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy) : IndepFun (fun ω => policy (fun i => Y i ω)) (Y t) μ := by
  exact BanditRL.OnlineLearning.history_policy_independent μ Y hY hind t policy hp

#check BanditRL.OnlineLearning.history_policy_independent
#print axioms BanditRL.OnlineLearning.history_policy_independent
def P011 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy) (hpb : ∀ z, policy z ∈ Set.Icc (0 : ℝ) 1)  : Prop :=  variance (Y t) μ ≤ ∫ ω, (policy (fun i => Y i ω) - Y t ω)^2 ∂μ
example : @P011 = @NeutralCoreAudit.Q011 := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy) (hpb : ∀ z, policy z ∈ Set.Icc (0 : ℝ) 1) : variance (Y t) μ ≤ ∫ ω, (policy (fun i => Y i ω) - Y t ω)^2 ∂μ := by
  exact BanditRL.OnlineLearning.history_policy_loss_ge_variance μ Y hY hind hb t policy hp hpb

#check BanditRL.OnlineLearning.history_policy_loss_ge_variance
#print axioms BanditRL.OnlineLearning.history_policy_loss_ge_variance
def P012 (total variance : ℝ) (T : ℕ) (hT : 0 < T)  : Prop :=  total / T - variance = (total - T * variance) / T
example : @P012 = @NeutralCoreAudit.Q012 := rfl
example (total variance : ℝ) (T : ℕ) (hT : 0 < T) : total / T - variance = (total - T * variance) / T := by
  exact BanditRL.OnlineLearning.normalized_excess total variance T hT

#check BanditRL.OnlineLearning.normalized_excess
#print axioms BanditRL.OnlineLearning.normalized_excess
example (y : ℕ → ℝ) (t : ℕ) : NeutralCoreAudit.D02 y t = meanPredict y t := rfl
end PublicCoreAudit
