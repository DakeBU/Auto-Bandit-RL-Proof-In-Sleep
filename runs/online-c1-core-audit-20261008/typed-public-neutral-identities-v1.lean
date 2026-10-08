import BanditRLProof.OnlineLearningHistory
import BanditRLProof.OnlineLearningFoundations
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

namespace PublicCoreAudit
end PublicCoreAudit
