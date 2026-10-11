import BanditRLProof.OnlineCumulativeOptimisticStability

noncomputable section
open Set Finset
namespace BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary
open BanditRL.OnlineConvex

def feasible : Set ℝ := Set.Icc (-1 : ℝ) 1
def regularizer (x : ℝ) : ℝ := x ^ 2 / 2
def hint (_ : ℝ) : ℝ := 0
def losses (_ : ℕ) (x : ℝ) : EReal := (x : EReal)
def predictionObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 0, losses i x + (hint x : EReal)
def currentObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 1, losses i x + extendedIndicator feasible x
def support : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

theorem tight_stability_at_nonminimizer :
    (currentObjective 0).toReal - (currentObjective (-1)).toReal ≤
      support ((0 : ℝ) - (-1)) - (1 / 2 : ℝ) * ‖(0 : ℝ) - (-1)‖ ^ 2 ∧
    IsMinOn predictionObjective feasible 0 ∧
    ¬ IsMinOn currentObjective feasible 0 ∧
    (∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z) ∧
    support ≠ 0 ∧
    (0 : ℝ) ∈ feasible ∧ (-1 : ℝ) ∈ feasible ∧ (2 : ℝ) ∉ feasible ∧
    currentObjective 0 = (0 : EReal) ∧
    currentObjective (-1) = ((-(1 / 2 : ℝ) : ℝ) : EReal) ∧
    currentObjective 2 = ⊤ ∧
    (currentObjective 0).toReal - (currentObjective (-1)).toReal = (1 / 2 : ℝ) ∧
    support ((0 : ℝ) - (-1)) - (1 / 2 : ℝ) * ‖(0 : ℝ) - (-1)‖ ^ 2 = (1 / 2 : ℝ) := by
  have h0 : (0 : ℝ) ∈ feasible := by norm_num [feasible]
  have hm1 : (-1 : ℝ) ∈ feasible := by norm_num [feasible]
  have hvalue (x : ℝ) (hx : x ∈ feasible) :
      currentObjective x = ((x ^ 2 / 2 + x : ℝ) : EReal) := by
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
    simp [losses, hint, support]
  have hbot : ∀ i < 0 + 1, ∀ x, losses i x ≠ ⊥ := by
    intro i hi x
    exact EReal.coe_ne_bot x
  have hdom : ∀ i < 0 + 1, feasible ⊆ effectiveDomain (losses i) := by
    intro i hi x hx
    exact EReal.coe_lt_top x
  have hstrong : ∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      currentObjective (a • x + (1 - a) • y) ≤
        (a : EReal) * currentObjective x + ((1 - a : ℝ) : EReal) * currentObjective y -
          (((1 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz := (convex_Icc (-1 : ℝ) 1) hx hy (le_of_lt ha)
      (by linarith : 0 ≤ 1 - a) (by ring : a + (1 - a) = 1)
    rw [hvalue _ hz, hvalue x hx, hvalue y hy]
    simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff,
      smul_eq_mul, Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    ring
  have bound := cumulative_optimistic_stability feasible (convex_Icc _ _) regularizer hint
    losses 0 1 hbot hdom (by norm_num) hstrong 0 h0 hprediction support hdifference (-1) hm1
  have hzero : currentObjective 0 = (0 : EReal) := by rw [hvalue 0 h0]; norm_num
  have hminus : currentObjective (-1) = ((-(1 / 2 : ℝ) : ℝ) : EReal) := by
    rw [hvalue (-1) hm1]
    norm_num
  refine ⟨bound, hprediction, ?_, hdifference, ?_, h0, hm1, ?_, hzero, hminus, ?_, ?_, ?_⟩
  · intro hm
    have h := hm hm1
    change currentObjective 0 ≤ currentObjective (-1) at h
    rw [hzero, hminus] at h
    norm_num at h
  · intro h
    have hh := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) h
    norm_num [support] at hh
  · norm_num [feasible]
  · norm_num [currentObjective, regularizer, losses, extendedIndicator, feasible]
  · rw [hzero, hminus]
    norm_num
  · norm_num [support]


end BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary
