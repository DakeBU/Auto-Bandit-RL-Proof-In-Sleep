import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Telescoping exponential estimate for dyadic peeling

A convex-exponential comparison gives a dyadic sum estimate strong enough
to imply the constant 15 used in source Lemma 9.3.
-/

namespace BanditRLProof.Concentration

open Real Finset
open scoped ENNReal NNReal

/-- A telescoping majorant obtained from `x/3 ≤ sinh(x/3)`. -/
theorem mul_exp_neg_le_exp_difference (x : ℝ) (hx : 0 ≤ x) :
    x * exp (-x) ≤ (3 / 2 : ℝ) * (exp (-(2 * x / 3)) - exp (-(4 * x / 3))) := by
  have hs : x / 3 ≤ sinh (x / 3) := self_le_sinh_iff.mpr (by positivity)
  rw [sinh_eq] at hs
  have h := mul_le_mul_of_nonneg_right hs (exp_pos (-x)).le
  have h1 : exp (x / 3) * exp (-x) = exp (-(2 * x / 3)) := by
    rw [← exp_add]
    congr 1
    ring
  have h2 : exp (-(x / 3)) * exp (-x) = exp (-(4 * x / 3)) := by
    rw [← exp_add]
    congr 1
    ring
  have heq : (exp (x / 3) - exp (-(x / 3))) / 2 * exp (-x) =
      (exp (-(2 * x / 3)) - exp (-(4 * x / 3))) / 2 := by
    rw [div_mul_eq_mul_div, sub_mul, h1, h2]
  rw [heq] at h
  nlinarith

/-- Finite dyadic exponential sum, with the remaining terminal mass retained. -/
theorem sum_dyadic_mul_exp_neg_le (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∑ j ∈ range N, (2 : ℝ) ^ j * exp (-(a * 2 ^ j)) ≤
      3 / (2 * a) * (exp (-(2 * a / 3)) - exp (-(2 * (a * 2 ^ N) / 3))) := by
  have hterm (j : ℕ) : (2 : ℝ) ^ j * exp (-(a * 2 ^ j)) ≤
      3 / (2 * a) *
        (exp (-(2 * (a * 2 ^ j) / 3)) - exp (-(2 * (a * 2 ^ (j+1)) / 3))) := by
    have h := mul_exp_neg_le_exp_difference (a * 2 ^ j) (by positivity)
    have heq : 4 * (a * (2 : ℝ) ^ j) / 3 = 2 * (a * 2 ^ (j+1)) / 3 := by
      rw [pow_succ]
      ring
    rw [heq] at h
    have h' := (div_le_div_iff_of_pos_right ha).mpr h
    convert h' using 1 <;> field_simp <;> ring
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have h := hterm N
    linarith

/-- Uniform finite-prefix bound; no logarithm or integral comparison loss. -/
theorem sum_dyadic_mul_exp_neg_le_three_div_two (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∑ j ∈ range N, (2 : ℝ) ^ j * exp (-(a * 2 ^ j)) ≤ 3 / (2 * a) := by
  have h := sum_dyadic_mul_exp_neg_le a ha N
  have he : exp (-(2 * a / 3)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hn := (exp_pos (-(2 * (a * 2 ^ N) / 3))).le
  have hp : 0 ≤ 3 / (2 * a) := by positivity
  nlinarith

/-- Countable dyadic sum in the probability-friendly extended nonnegative reals. -/
theorem tsum_dyadic_mul_exp_neg_le (a : ℝ) (ha : 0 < a) :
    (∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ j * exp (-(a * 2 ^ j)))) ≤
      ENNReal.ofReal (3 / (2 * a)) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (sum_dyadic_mul_exp_neg_le_three_div_two a ha N)

/-- The geometric series in source Lemma 9.3 is at most 12 delta/gap^2. -/
theorem sum_moss_peeling_exponential_le_twelve (δ gap : ℝ)
    (hδ : 0 ≤ δ) (hgap : 0 < gap) (N : ℕ) :
    ∑ j ∈ range N, δ * (2 : ℝ) ^ (j+1) * exp (-(gap ^ 2 / 4 * 2 ^ j)) ≤
      12 * δ / gap ^ 2 := by
  have ha : 0 < gap ^ 2 / 4 := by positivity
  have h := mul_le_mul_of_nonneg_left
    (sum_dyadic_mul_exp_neg_le_three_div_two (gap ^ 2 / 4) ha N)
    (show 0 ≤ 2 * δ by positivity)
  have heq : (∑ j ∈ range N, δ * (2 : ℝ) ^ (j+1) * exp (-(gap ^ 2 / 4 * 2 ^ j))) =
      2 * δ * ∑ j ∈ range N, (2 : ℝ) ^ j * exp (-(gap ^ 2 / 4 * 2 ^ j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  rw [heq]
  convert h using 1 <;> field_simp <;> ring

/-- Source-constant countable series bound, with no weakened constant. -/
theorem tsum_moss_peeling_exponential_le_fifteen (δ gap : ℝ)
    (hδ : 0 ≤ δ) (hgap : 0 < gap) :
    (∑' j : ℕ, ENNReal.ofReal
      (δ * (2 : ℝ) ^ (j+1) * exp (-(gap ^ 2 / 4 * 2 ^ j)))) ≤
      ENNReal.ofReal (15 * δ / gap ^ 2) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine (sum_moss_peeling_exponential_le_twelve δ gap hδ hgap N).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg gap)
  nlinarith

end BanditRLProof.Concentration
