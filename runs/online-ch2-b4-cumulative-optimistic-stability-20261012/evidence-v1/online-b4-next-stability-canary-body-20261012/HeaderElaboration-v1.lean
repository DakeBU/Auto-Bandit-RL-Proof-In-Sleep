import CumulativeOptimisticStabilityCandidate

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

#check (    (currentObjective 0).toReal - (currentObjective (-1)).toReal ≤
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
    support ((0 : ℝ) - (-1)) - (1 / 2 : ℝ) * ‖(0 : ℝ) - (-1)‖ ^ 2 = (1 / 2 : ℝ)
)

end BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary
