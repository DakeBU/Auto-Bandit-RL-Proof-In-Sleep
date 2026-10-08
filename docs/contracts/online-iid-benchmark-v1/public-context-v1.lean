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
