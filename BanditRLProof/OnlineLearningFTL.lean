import BanditRLProof.OnlineLearningFoundations
import BanditRLProof.OnlineLearningMean
import Mathlib.NumberTheory.Harmonic.Bounds

namespace BanditRL.OnlineLearning

/-- Source round t+1 prediction: initial 1/2, then the mean of exactly t past observations. -/
noncomputable def meanPredict (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1/2 else empiricalMean y t

/-- Strict-prefix causality, including the fixed initial prediction. -/
theorem meanPredict_prefix (y z : ℕ → ℝ) (t : ℕ) (h : ∀ i < t, y i = z i) :
    meanPredict y t = meanPredict z t := by
  unfold meanPredict empiricalMean
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact h i (Finset.mem_range.mp hi)

/-- The actual prediction is feasible. -/
theorem meanPredict_mem (y : ℕ → ℝ) (t : ℕ)
    (hy : ∀ i < t, y i ∈ Set.Icc (0 : ℝ) 1) :
    meanPredict y t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold meanPredict
  split_ifs with h
  · norm_num
  · exact empiricalMean_mem y t (Nat.pos_of_ne_zero h) hy

/-- Updating the sufficient statistic adds only the current observation. -/
theorem empiricalMean_update (y : ℕ → ℝ) (t : ℕ) (ht : 0 < t) :
    empiricalMean y (t+1) = empiricalMean y t +
      (y t - empiricalMean y t) / (t+1) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht
  have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
  unfold empiricalMean
  rw [Finset.sum_range_succ]
  push_cast
  field_simp
  ring

/-- Source stability bound, zero-based index; the special initial round is included. -/
theorem meanPredict_stability (y : ℕ → ℝ) (t : ℕ)
    (hy : ∀ i ≤ t, y i ∈ Set.Icc (0 : ℝ) 1) :
    (meanPredict y t - y t)^2 - (empiricalMean y (t+1) - y t)^2 ≤
      4 / (t+1) := by
  by_cases ht : t = 0
  · subst t
    have hy0 := hy 0 le_rfl
    norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
    nlinarith [sq_nonneg (y 0), mul_nonneg hy0.1 (sub_nonneg.mpr hy0.2)]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have ha := empiricalMean_mem y t htpos (fun i hi => hy i (Nat.le_of_lt hi))
    have hb := hy t le_rfl
    have hd : 0 < (t : ℝ) + 1 := by positivity
    have hd1 : 1 ≤ (t : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) t; linarith
    have hs : (empiricalMean y t - y t)^2 ≤ 1 := by
      have hlo : -1 ≤ empiricalMean y t - y t := by linarith [ha.1, hb.2]
      have hhi : empiricalMean y t - y t ≤ 1 := by linarith [ha.2, hb.1]
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0 ≤ 1 + (empiricalMean y t - y t))]
    rw [meanPredict, if_neg ht, empiricalMean_update y t htpos]
    have hid : (empiricalMean y t - y t)^2 -
        (empiricalMean y t + (y t - empiricalMean y t) / (t+1) - y t)^2 =
        (2 / (t+1) - 1 / (t+1)^2) * (empiricalMean y t - y t)^2 := by
      field_simp
      ring
    rw [hid]
    have hcoef : 0 ≤ 2 / ((t : ℝ)+1) - 1 / ((t : ℝ)+1)^2 := by
      have heq : 2 / ((t : ℝ)+1) - 1 / ((t : ℝ)+1)^2 =
          (2*((t : ℝ)+1)-1)/((t : ℝ)+1)^2 := by field_simp
      rw [heq]
      exact div_nonneg (by linarith) (sq_nonneg _)
    have hbound := mul_le_mul_of_nonneg_left hs hcoef
    have hneg : 0 ≤ 1 / ((t : ℝ)+1)^2 := by positivity
    have htwo : 0 ≤ 2 / ((t : ℝ)+1) := by positivity
    have hfour : 4 / ((t : ℝ)+1) = 2 * (2 / ((t : ℝ)+1)) := by ring
    rw [hfour]
    nlinarith

/-- Orabona Theorem 1.3: actual past-average predictor versus the best fixed
prediction, represented by its proved empirical-mean minimizer. -/
theorem theorem_1_3 (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    (∑ t ∈ Finset.range T, (meanPredict y t - y t)^2) -
      (∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2) ≤
        4 + 4 * Real.log T := by
  have hleader := lemma_1_2 Set.univ (fun t x => (x - y t)^2)
    (empiricalMean y) T (by simp)
    (fun n hn hnT u hu => empiricalMean_minimizes y n hn u)
  have hstep := Finset.sum_le_sum (s := Finset.range T)
    (fun t ht => meanPredict_stability y t (fun i hi => hy i
      (lt_of_le_of_lt hi (Finset.mem_range.mp ht))))
  have hsum : (∑ t ∈ Finset.range T, (4:ℝ) / (t+1)) = 4 * (harmonic T : ℝ) := by
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum, div_eq_mul_inv]
  rw [Finset.sum_sub_distrib, hsum] at hstep
  have hh := harmonic_le_one_add_log T
  linarith

end BanditRL.OnlineLearning
