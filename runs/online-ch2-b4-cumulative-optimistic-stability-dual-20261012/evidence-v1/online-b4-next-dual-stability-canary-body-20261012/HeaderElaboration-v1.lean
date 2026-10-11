import CumulativeOptimisticStabilityDualCandidate

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
#check
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
    ‖support‖ ^ 2 / (2 * (1 : ℝ)) = (2 : ℝ)
end Tight

namespace ZeroCurvature
#check
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
      ‖support‖ ^ 2 / (2 * (0 : ℝ)))
end ZeroCurvature

end BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary
