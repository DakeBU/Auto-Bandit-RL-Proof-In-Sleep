import BanditRLProof.OnlineCumulativeOptimisticStabilityDual

noncomputable section
open Set Finset
namespace BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary
open BanditRL.OnlineConvex

namespace Tight
def feasible : Set ℝ := Set.Icc (-2 : ℝ) 2
def regularizer (x : ℝ) : ℝ := x ^ 2 / 2
def hint (_ : ℝ) : ℝ := 0
def losses (_ : ℕ) (x : ℝ) : EReal := ((2 * x : ℝ) : EReal)
def predictionObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 0, losses i x + (hint x : EReal)
def currentObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 1, losses i x + extendedIndicator feasible x
def support : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
end Tight

namespace ZeroCurvature
def feasible : Set ℝ := Set.Icc (-1 : ℝ) 1
def regularizer (_ : ℝ) : ℝ := 0
def hint (_ : ℝ) : ℝ := 0
def losses (_ : ℕ) (x : ℝ) : EReal := (x : EReal)
def predictionObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 0, losses i x + (hint x : EReal)
def currentObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 1, losses i x + extendedIndicator feasible x
def support : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
end ZeroCurvature

namespace Tight
theorem tight_dual_stability_at_nonminimizer :
    (currentObjective 0).toReal - (currentObjective (-2)).toReal ≤
      ‖support‖ ^ 2 / (2 * (1 : ℝ)) ∧
    IsMinOn predictionObjective feasible 0 ∧
    ¬ IsMinOn currentObjective feasible 0 ∧
    (∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z) ∧
    support ≠ 0 ∧ ‖support‖ = (2 : ℝ) ∧
    (0 : ℝ) ∈ feasible ∧ (-2 : ℝ) ∈ feasible ∧ (3 : ℝ) ∉ feasible ∧
    currentObjective 0 = (0 : EReal) ∧
    currentObjective (-2) = ((-2 : ℝ) : EReal) ∧
    currentObjective 3 = ⊤ ∧
    (currentObjective 0).toReal - (currentObjective (-2)).toReal = (2 : ℝ) ∧
    ‖support‖ ^ 2 / (2 * (1 : ℝ)) = (2 : ℝ) := by
  have h0 : (0 : ℝ) ∈ feasible := by norm_num [feasible]
  have hm2 : (-2 : ℝ) ∈ feasible := by norm_num [feasible]
  have hvalue (x : ℝ) (hx : x ∈ feasible) :
      currentObjective x = ((x ^ 2 / 2 + 2 * x : ℝ) : EReal) := by
    simp [currentObjective, regularizer, losses, extendedIndicator, hx]
  have hprediction : IsMinOn predictionObjective feasible 0 := by
    intro z hz
    change predictionObjective 0 ≤ predictionObjective z
    simp only [predictionObjective, sum_range_zero, add_zero, hint, EReal.coe_zero,
      regularizer, zero_pow (by decide : 2 ≠ 0), zero_div, EReal.coe_le_coe_iff]
    positivity
  have hdifference : ∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z := by
    intro z hz
    simp only [losses, EReal.toReal_coe, hint]
    simp [support]
  have hbot : ∀ i < 0 + 1, ∀ x, losses i x ≠ ⊥ := by
    intro i hi x
    exact EReal.coe_ne_bot (2 * x)
  have hdom : ∀ i < 0 + 1, feasible ⊆ effectiveDomain (losses i) := by
    intro i hi x hx
    exact EReal.coe_lt_top (2 * x)
  have hstrong : ∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      currentObjective (a • x + (1 - a) • y) ≤
        (a : EReal) * currentObjective x + ((1 - a : ℝ) : EReal) * currentObjective y -
          (((1 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz := (convex_Icc (-2 : ℝ) 2) hx hy (le_of_lt ha)
      (by linarith : 0 ≤ 1 - a) (by ring : a + (1 - a) = 1)
    rw [hvalue _ hz, hvalue x hx, hvalue y hy]
    simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff,
      smul_eq_mul, Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    ring
  have hV : Convex ℝ feasible := convex_Icc _ _
  have hlam : 0 < (1 : ℝ) := by norm_num
  have bound := cumulative_optimistic_stability_dual_bound feasible hV regularizer hint
    losses 0 1 hbot hdom hlam hstrong 0 h0 hprediction support hdifference (-2) hm2
  have hzero : currentObjective 0 = (0 : EReal) := by rw [hvalue 0 h0]; norm_num
  have hminus : currentObjective (-2) = ((-2 : ℝ) : EReal) := by
    rw [hvalue (-2) hm2]
    norm_num
  have hnorm : ‖support‖ = (2 : ℝ) := by
    norm_num [support, norm_smul, ContinuousLinearMap.norm_id]
  refine ⟨bound, hprediction, ?_, hdifference, ?_, hnorm, h0, hm2, ?_, hzero, hminus, ?_, ?_, ?_⟩
  · intro hm
    have h := hm hm2
    change currentObjective 0 ≤ currentObjective (-2) at h
    rw [hzero, hminus] at h
    norm_num at h
  · intro h
    have hh := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) h
    norm_num [support] at hh
  · norm_num [feasible]
  · norm_num [currentObjective, regularizer, losses, extendedIndicator, feasible]
  · rw [hzero, hminus]
    norm_num
  · rw [hnorm]
    norm_num

end Tight

namespace ZeroCurvature
theorem zero_curvature_division_is_false :
    Convex ℝ feasible ∧
    (∀ i < (0 : ℕ) + 1, ∀ x, losses i x ≠ ⊥) ∧
    (∀ i < (0 : ℕ) + 1, feasible ⊆ effectiveDomain (losses i)) ∧
    (∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      currentObjective (a • x + (1 - a) • y) ≤
        (a : EReal) * currentObjective x + ((1 - a : ℝ) : EReal) * currentObjective y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ∧
    IsMinOn predictionObjective feasible 0 ∧
    (∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z) ∧
    (0 : ℝ) ∈ feasible ∧ (-1 : ℝ) ∈ feasible ∧
    ‖support‖ = (1 : ℝ) ∧
    currentObjective 0 = (0 : EReal) ∧
    currentObjective (-1) = ((-1 : ℝ) : EReal) ∧
    (currentObjective 0).toReal - (currentObjective (-1)).toReal = (1 : ℝ) ∧
    ‖support‖ ^ 2 / (2 * (0 : ℝ)) = (0 : ℝ) ∧
    ¬ ((currentObjective 0).toReal - (currentObjective (-1)).toReal ≤
      ‖support‖ ^ 2 / (2 * (0 : ℝ))) := by
  have h0 : (0 : ℝ) ∈ feasible := by norm_num [feasible]
  have hm1 : (-1 : ℝ) ∈ feasible := by norm_num [feasible]
  have hvalue (x : ℝ) (hx : x ∈ feasible) : currentObjective x = (x : EReal) := by
    simp [currentObjective, regularizer, losses, extendedIndicator, hx]
  have hprediction : IsMinOn predictionObjective feasible 0 := by
    intro z hz
    simp [predictionObjective, regularizer, hint]
  have hdifference : ∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z := by
    intro z hz
    simp [losses, hint, support]
  have hbot : ∀ i < (0 : ℕ) + 1, ∀ x, losses i x ≠ ⊥ := by
    intro i hi x
    exact EReal.coe_ne_bot x
  have hdom : ∀ i < (0 : ℕ) + 1, feasible ⊆ effectiveDomain (losses i) := by
    intro i hi x hx
    exact EReal.coe_lt_top x
  have hstrong : ∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      currentObjective (a • x + (1 - a) • y) ≤
        (a : EReal) * currentObjective x + ((1 - a : ℝ) : EReal) * currentObjective y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz := (convex_Icc (-1 : ℝ) 1) hx hy (le_of_lt ha)
      (by linarith : 0 ≤ 1 - a) (by ring : a + (1 - a) = 1)
    rw [hvalue _ hz, hvalue x hx, hvalue y hy]
    simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff,
      smul_eq_mul]
    ring_nf
    exact le_rfl
  have hzero := hvalue 0 h0
  have hminus := hvalue (-1) hm1
  have hnorm : ‖support‖ = (1 : ℝ) := by simp [support, ContinuousLinearMap.norm_id]
  refine ⟨convex_Icc _ _, hbot, hdom, hstrong, hprediction, hdifference,
    h0, hm1, hnorm, hzero, hminus, ?_, ?_, ?_⟩
  · rw [hzero, hminus]
    norm_num
  · norm_num
  · rw [hzero, hminus]
    norm_num

end ZeroCurvature

end BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary
