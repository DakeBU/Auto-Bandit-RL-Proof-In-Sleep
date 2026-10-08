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
