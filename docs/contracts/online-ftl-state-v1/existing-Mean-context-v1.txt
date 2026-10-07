import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace BanditRL.OnlineLearning

/-- Mean of the first n observations; zero is used only as the empty-prefix convention. -/
noncomputable def empiricalMean (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ t ∈ Finset.range n, y t) / n

/-- Exact squared-loss decomposition underlying Orabona v10 Chapter 1, printed p3. -/
theorem empiricalMean_decomposition (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ) :
    (∑ t ∈ Finset.range n, (u - y t)^2) =
      (∑ t ∈ Finset.range n, (empiricalMean y n - y t)^2) +
        n * (u - empiricalMean y n)^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hm : (n : ℝ) * empiricalMean y n = ∑ t ∈ Finset.range n, y t := by
    unfold empiricalMean
    field_simp
  have expand (a : ℝ) : (∑ t ∈ Finset.range n, (a - y t)^2) =
      n * a^2 - 2*a*(∑ t ∈ Finset.range n, y t) + ∑ t ∈ Finset.range n, (y t)^2 := by
    simp_rw [sub_sq]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [expand u, expand (empiricalMean y n), ← hm]
  ring

/-- The empirical mean is a global minimizer, hence also a feasible-set minimizer when feasible. -/
theorem empiricalMean_minimizes (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ) :
    (∑ t ∈ Finset.range n, (empiricalMean y n - y t)^2) ≤
      ∑ t ∈ Finset.range n, (u - y t)^2 := by
  rw [empiricalMean_decomposition y n hn u]
  have h : 0 ≤ (n : ℝ) * (u - empiricalMean y n)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

/-- Feasibility in the guessing game's interval. -/
theorem empiricalMean_mem (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hy : ∀ t < n, y t ∈ Set.Icc (0 : ℝ) 1) :
    empiricalMean y n ∈ Set.Icc (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun t ht => (hy t (Finset.mem_range.mp ht)).1)) hnR.le
  · apply (div_le_one hnR).2
    calc (∑ t ∈ Finset.range n, y t) ≤ ∑ t ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum (fun t ht => (hy t (Finset.mem_range.mp ht)).2)
      _ = n := by simp

/-- Positive-horizon cumulative squared loss has the unique empirical-mean minimizer. -/
theorem empiricalMean_unique (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ)
    (hu : (∑ t ∈ Finset.range n, (u-y t)^2) ≤
      ∑ t ∈ Finset.range n, (empiricalMean y n-y t)^2) :
    u = empiricalMean y n := by
  have hd := empiricalMean_decomposition y n hn u
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ) * (u - empiricalMean y n)^2 ≤ 0 := by linarith
  have hz : (u - empiricalMean y n)^2 = 0 := by
    by_contra hne
    have hs : 0 < (u - empiricalMean y n)^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    exact (not_lt_of_ge hp) (mul_pos hnR hs)
  nlinarith

end BanditRL.OnlineLearning
