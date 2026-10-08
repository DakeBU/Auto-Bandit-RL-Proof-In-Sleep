import BanditRLProof.OnlineGuessingRandomizedIID
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
universe u v w z
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
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) :
    C0 μ Y T = expectedFixedMinimum μ Y T := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y P : ℕ → Ω → ℝ) (T : ℕ) : C1 μ Y P T = expectedFixedRegret μ Y P T := rfl
example (y : ℕ → ℝ) (t : ℕ) : C2 y t = meanPredict y t := rfl
example : S001 = Q001 := rfl
example : S002 = Q002 := rfl
example : S003 = Q003 := rfl
example : S004 = Q004 := rfl
