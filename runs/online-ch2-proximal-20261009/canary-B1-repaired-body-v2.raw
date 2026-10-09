/-
Nondegenerate public instances of the real minimizer comparison helper.
Each instance proves its minimum and calls the same public production theorem.
These test families are not additional printed source results or an algorithm.
-/
import BanditRLProof.OnlineProximalComparison
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.NormNum
open Set
namespace BanditRL.OnlineProximalCanary

theorem nonsmooth_shifted_quadratic :
    IsMinOn (fun z : ℝ => |z| + (z - 1 / 2) ^ 2 / 2) univ 0 ∧
      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
      (∀ u : ℝ, -|u| ≤ -u / 2) ∧
      (-1 / 4 : ℝ) ≤ -1 / 8 := by
  have hm : IsMinOn (fun z : ℝ => |z| + (z - 1 / 2) ^ 2 / 2) univ 0 := by
    intro z hz
    change |(0 : ℝ)| + (0 - 1 / 2) ^ 2 / 2 ≤ |z| + (z - 1 / 2) ^ 2 / 2
    by_cases hz' : 0 ≤ z
    · rw [abs_of_nonneg hz']
      norm_num only [abs_zero]
      nlinarith [sq_nonneg z]
    · rw [abs_of_nonpos (le_of_not_ge hz')]
      norm_num only [abs_zero]
      nlinarith [sq_nonneg z]
  have hf : ConvexOn ℝ (univ : Set ℝ) (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using
      (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℝ)))
  have hd : HasDerivAt (fun z : ℝ => (z - 1 / 2) ^ 2 / 2) (-1 / 2) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).sub_const (1 / 2)).pow 2).div_const 2 using 1 <;>
      norm_num
  have hb : ∀ u : ℝ, -|u| ≤ -u / 2 := by
    intro u
    have hh := OnlineProximal.convex_minimizer_comparison univ abs
      (fun z : ℝ => (z - 1 / 2) ^ 2 / 2) 0 (mem_univ 0) hf hm
      (ContinuousLinearMap.toSpanSingleton ℝ (-1 / 2)) hd.hasFDerivAt u (mem_univ u)
    norm_num [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hh
    nlinarith only [hh]
  refine ⟨hm, not_differentiableAt_abs_zero, hb, ?_⟩
  have hh := hb (1 / 4)
  have hl : -|(1 / 4 : ℝ)| = -1 / 4 := by norm_num
  have hr : -(1 / 4 : ℝ) / 2 = -1 / 8 := by norm_num
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh

theorem boundary_linear_regularizer :
    IsMinOn (fun z : ℝ => z + (-z / 2)) (Icc 0 1) 0 ∧
      (∀ u ∈ Icc (0 : ℝ) 1, -u ≤ -u / 2) ∧
      ¬ IsMinOn (fun z : ℝ => z + (-z / 2)) univ 0 := by
  have hm : IsMinOn (fun z : ℝ => z + (-z / 2)) (Icc 0 1) 0 := by
    intro z hz
    change (0 : ℝ) + (-0 / 2) ≤ z + (-z / 2)
    linarith [hz.1]
  have hd : HasDerivAt (fun z : ℝ => -z / 2) (-1 / 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg.div_const 2
  have hb : ∀ u ∈ Icc (0 : ℝ) 1, -u ≤ -u / 2 := by
    intro u hu
    have hh := OnlineProximal.convex_minimizer_comparison (Icc 0 1) (fun z : ℝ => z)
      (fun z : ℝ => -z / 2) 0 (by simp)
      (convexOn_id (convex_Icc (0 : ℝ) 1)) hm
      (ContinuousLinearMap.toSpanSingleton ℝ (-1 / 2)) hd.hasFDerivAt u hu
    norm_num [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hh
    nlinarith only [hh]
  refine ⟨hm, hb, ?_⟩
  intro hn
  have hh := hn (mem_univ (-1 : ℝ))
  norm_num at hh

theorem nonconvex_regularizer :
    IsMinOn (fun z : ℝ => z ^ 2 + (-z ^ 2 / 2 + z)) univ (-1) ∧
      ¬ ConvexOn ℝ univ (fun z : ℝ => -z ^ 2 / 2 + z) ∧
      (∀ u : ℝ, 1 - u ^ 2 ≤ 2 * (u + 1)) ∧
      (1 : ℝ) ≤ 2 := by
  have hm : IsMinOn (fun z : ℝ => z ^ 2 + (-z ^ 2 / 2 + z)) univ (-1) := by
    intro z hz
    change (-1 : ℝ) ^ 2 + (-(-1 : ℝ) ^ 2 / 2 + (-1)) ≤ z ^ 2 + (-z ^ 2 / 2 + z)
    nlinarith [sq_nonneg (z + 1)]
  have hnc : ¬ ConvexOn ℝ univ (fun z : ℝ => -z ^ 2 / 2 + z) := by
    intro hc
    have hh := hc.2 (mem_univ (-1 : ℝ)) (mem_univ (1 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    norm_num at hh
  have hd : HasDerivAt (fun z : ℝ => -z ^ 2 / 2 + z) 2 (-1) := by
    convert ((((hasDerivAt_id (-1 : ℝ)).pow 2).neg.div_const 2).add
      (hasDerivAt_id (-1 : ℝ))) using 1 <;> norm_num
  have hb : ∀ u : ℝ, 1 - u ^ 2 ≤ 2 * (u + 1) := by
    intro u
    have hh := OnlineProximal.convex_minimizer_comparison univ (fun z : ℝ => z ^ 2)
      (fun z : ℝ => -z ^ 2 / 2 + z) (-1) (mem_univ (-1))
      (Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)) hm
      (ContinuousLinearMap.toSpanSingleton ℝ 2) hd.hasFDerivAt u (mem_univ u)
    norm_num [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hh
    nlinarith only [hh]
  refine ⟨hm, hnc, hb, ?_⟩
  have hh := hb 0
  have hl : (1 : ℝ) - 0 ^ 2 = 1 := by norm_num
  have hr : (2 : ℝ) * (0 + 1) = 2 := by norm_num
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh

end BanditRL.OnlineProximalCanary
