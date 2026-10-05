/-
Source: Orabona, Online Learning, arXiv:1912.13213v10, Example 2.10,
printed p.12 / PDF p.24. This retained implementation uses zero-based time:
Lean 0 is source round 1. The exceptional first coefficient is -1/2; later
Lean odd/even coefficients are +1 and -1. Every feasible initial x0 is allowed.

prefixCoefficient and linearFTLPredict are actual recursive-past definitions.
The prefix theorem proves causality for a fixed x0. Generic positive-time
zero-prefix ties select -1, a permitted concrete FTL selection; the source
failure stream has no such ties. The historical objective inequality alone
does not require feasible x0 at time 0 because both objectives are empty.
Combine linearFTLPredict_mem with linearFTLPredict_minimizes for feasible FTL.

example_2_10 proves the actual played-loss regret against comparator 0, exactly
T - 1 - x0/2 and at least T - 3/2, for T >= 1. It is a counterexample for this
FTL family, not a lower bound for every online algorithm. The six helpers and
three definitions are library refinements of one printed example. This
migration preserves all existing definition, statement and proof code.
-/
import BanditRLProof.OnlineLearningFTL
import Mathlib.Tactic

noncomputable section
open Set Finset
namespace BanditRL.OnlineLearning

def prefixCoefficient (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t+1 => prefixCoefficient z t + z t

def linearFTLPredict (z : ℕ → ℝ) (x0 : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then x0 else if prefixCoefficient z t < 0 then 1 else -1

def failureCoefficient (t : ℕ) : ℝ :=
  if t = 0 then -(1/2) else if t % 2 = 1 then 1 else -1

theorem prefixCoefficient_eq_sum (z : ℕ → ℝ) (t : ℕ) :
    prefixCoefficient z t = ∑ i ∈ range t, z i := by
  induction t with
  | zero => simp [prefixCoefficient]
  | succ t ih => simp [prefixCoefficient, sum_range_succ, ih]

theorem linearFTLPredict_prefix (z w : ℕ → ℝ) (x0 : ℝ) (t : ℕ)
    (h : ∀ i < t, z i = w i) : linearFTLPredict z x0 t = linearFTLPredict w x0 t := by
  have he : prefixCoefficient z t = prefixCoefficient w t := by
    rw [prefixCoefficient_eq_sum, prefixCoefficient_eq_sum]
    apply sum_congr rfl
    intro i hi
    exact h i (mem_range.mp hi)
  simp only [linearFTLPredict, he]

theorem linearFTLPredict_mem (z : ℕ → ℝ) (x0 : ℝ) (hx0 : x0 ∈ Icc (-1 : ℝ) 1)
    (t : ℕ) : linearFTLPredict z x0 t ∈ Icc (-1 : ℝ) 1 := by
  unfold linearFTLPredict
  split_ifs <;> simp_all

theorem linearFTLPredict_minimizes (z : ℕ → ℝ) (x0 : ℝ) (t : ℕ)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (∑ i ∈ range t, z i * linearFTLPredict z x0 t) ≤ ∑ i ∈ range t, z i * u := by
  rw [← sum_mul, ← sum_mul, ← prefixCoefficient_eq_sum]
  by_cases ht : t = 0
  · subst t; simp [prefixCoefficient]
  · unfold linearFTLPredict
    rw [if_neg ht]
    split_ifs with hz
    · exact mul_le_mul_of_nonpos_left hu.2 hz.le
    · exact mul_le_mul_of_nonneg_left hu.1 (le_of_not_gt hz)

theorem failure_prefixCoefficient (t : ℕ) (ht : 0 < t) :
    prefixCoefficient failureCoefficient t = if t % 2 = 1 then -(1/2) else (1/2) := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hz : t = 0
    · subst t; norm_num [prefixCoefficient, failureCoefficient]
    · have htpos : 0 < t := Nat.pos_of_ne_zero hz
      rw [prefixCoefficient, ih htpos]
      unfold failureCoefficient
      rw [if_neg hz]
      have hm := Nat.mod_lt t (by decide : 0 < 2)
      split_ifs <;> norm_num at * <;> omega

theorem failure_prediction (x0 : ℝ) (t : ℕ) (ht : 0 < t) :
    linearFTLPredict failureCoefficient x0 t = if t % 2 = 1 then 1 else -1 := by
  unfold linearFTLPredict
  rw [if_neg (Nat.ne_of_gt ht), failure_prefixCoefficient t ht]
  split_ifs <;> norm_num at *

theorem example_2_10 (x0 : ℝ) (hx0 : x0 ∈ Icc (-1 : ℝ) 1) (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ range T, failureCoefficient t * linearFTLPredict failureCoefficient x0 t) -
      (∑ t ∈ range T, failureCoefficient t * (0 : ℝ)) = (T : ℝ) - 1 - x0 / 2 ∧
    (T : ℝ) - 3/2 ≤
      (∑ t ∈ range T, failureCoefficient t * linearFTLPredict failureCoefficient x0 t) -
        (∑ t ∈ range T, failureCoefficient t * (0 : ℝ)) := by
  have hloss (t : ℕ) (ht : 0 < t) :
      failureCoefficient t * linearFTLPredict failureCoefficient x0 t = 1 := by
    rw [failure_prediction x0 t ht]
    unfold failureCoefficient
    rw [if_neg (Nat.ne_of_gt ht)]
    split_ifs <;> norm_num
  have he (n : ℕ) :
      (∑ t ∈ range (n+1), failureCoefficient t * linearFTLPredict failureCoefficient x0 t) =
      (n : ℝ) - x0/2 := by
    induction n with
    | zero => simp [failureCoefficient, linearFTLPredict]; ring
    | succ n ih =>
      rw [sum_range_succ, ih, hloss (n+1) (Nat.zero_lt_succ n)]
      push_cast
      ring
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  simp only [mul_zero, sum_const_zero, sub_zero]
  rw [he]
  constructor
  · push_cast; ring
  · have hx := hx0.2
    push_cast
    linarith

end BanditRL.OnlineLearning
