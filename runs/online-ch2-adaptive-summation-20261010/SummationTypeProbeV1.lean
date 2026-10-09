import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
open Set Finset MeasureTheory

namespace BanditRL.OnlineAdaptiveSummation

#check (∀ (a₀ : ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℕ),
    0 ≤ a₀ → (∀ t < T, 0 ≤ a t) →
    ContinuousOn f (Ici 0) → AntitoneOn f (Ici 0) →
    (∀ x ∈ Ici 0, 0 ≤ f x) →
    (∑ t ∈ range T, a t * f (a₀ + ∑ i ∈ range (t + 1), a i)) ≤
      ∫ x in a₀..(a₀ + ∑ i ∈ range T, a i), f x)
#check ContinuousOn.intervalIntegrable_of_Icc
#check intervalIntegral.integral_mono_on
#check intervalIntegral.sum_integral_adjacent_intervals
#check intervalIntegral.integral_const
end BanditRL.OnlineAdaptiveSummation
