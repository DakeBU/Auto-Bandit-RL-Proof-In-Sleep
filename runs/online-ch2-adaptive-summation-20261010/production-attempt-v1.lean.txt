import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
open Set Finset MeasureTheory

namespace BanditRL.OnlineAdaptiveSummation

theorem lemma_4_13 (a₀ : ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℕ)
    (h₀ : 0 ≤ a₀) (ha : ∀ t < T, 0 ≤ a t)
    (hcont : ContinuousOn f (Set.Ici 0)) (hmono : AntitoneOn f (Set.Ici 0))
    (hf : ∀ x ∈ Set.Ici 0, 0 ≤ f x) :
    (∑ t ∈ range T, a t * f (a₀ + ∑ i ∈ range (t + 1), a i)) ≤
      ∫ x in a₀..(a₀ + ∑ i ∈ range T, a i), f x := by
  let s : ℕ → ℝ := fun n => a₀ + ∑ i ∈ range n, a i
  have hs_nonneg (n : ℕ) (hn : n ≤ T) : 0 ≤ s n := by
    apply add_nonneg h₀
    exact sum_nonneg fun i hi => ha i ((mem_range.mp hi).trans_le hn)
  have hs_step (t : ℕ) : s (t + 1) - s t = a t := by
    dsimp [s]
    rw [sum_range_succ]
    ring
  have hs_le (t : ℕ) (ht : t < T) : s t ≤ s (t + 1) := by
    have := ha t ht
    linarith [hs_step t]
  have hfi (t : ℕ) (ht : t < T) :
      IntervalIntegrable f volume (s t) (s (t + 1)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (hs_le t ht)
    apply hcont.mono
    intro x hx
    exact (hs_nonneg t (Nat.le_of_lt ht)).trans hx.1
  have hpoint (t : ℕ) (ht : t < T) :
      a t * f (s (t + 1)) ≤ ∫ x in s t..s (t + 1), f x := by
    have h := intervalIntegral.integral_mono_on (hs_le t ht)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f (s (t + 1)))
        volume (s t) (s (t + 1))) (hfi t ht) (fun x hx =>
          hmono ((hs_nonneg t (Nat.le_of_lt ht)).trans hx.1)
            (hs_nonneg (t + 1) ht) hx.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hs_step t] using h
  have hsum := sum_le_sum fun t ht => hpoint t (mem_range.mp ht)
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun t ht => hfi t ht)] at hsum
  simpa [s] using hsum

end BanditRL.OnlineAdaptiveSummation
