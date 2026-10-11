import BanditRLProof.OnlineAdaptiveBenchmark
import BanditRLProof.OnlineGuessingOGD

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineAdaptiveOSD
namespace AdaptiveProbe
abbrev V := BanditRL.OnlineGradientDescent.unitInterval

def W : Domain (E := ℝ) where
  carrier := {0}
  nonempty := ⟨0, rfl⟩
  closed := isClosed_singleton
  convex := convex_singleton 0

def feedback (t : ℕ) : ℝ := if t = 1 then 3 else if t = 3 then -4 else 0
def loss (t : ℕ) (x : ℝ) : EReal := ((feedback t * x : ℝ) : EReal)
def policy : SupportPolicy (E := ℝ) := fun t _ _ _ => feedback t
def futureLoss (t : ℕ) (x : ℝ) : EReal := if t < 2 then loss t x else (7 : EReal)
def zeroLoss (_ : ℕ) (_ : ℝ) : EReal := 0
def zeroPolicy : SupportPolicy (E := ℝ) := fun _ _ _ _ => 0
abbrev x (α : ℝ) (t : ℕ) := output V α 1 loss (1 / 2) policy t
abbrev q (α : ℝ) (t : ℕ) := energy V α 1 loss (1 / 2) policy t
abbrev r (α : ℝ) (t : ℕ) := eta V α 1 loss (1 / 2) policy t
#check (∀ (U : Domain (E := ℝ)) (t : ℕ),
    IsConvexExtended (loss t) ∧
    BanditRL.OnlineSubgradientDescent.SubdifferentiableOn U (loss t) ∧
    ∀ z : ℝ, feedback t ∈ SourceSubdifferential (loss t) z)
#check ((∀ α : ℝ, ∀ t : ℕ, selected V α 1 loss (1 / 2) policy t = feedback t) ∧
    (∀ α : ℝ, ∀ T : ℕ, T ≤ 4 →
      q α T = if T ≤ 1 then 0 else if T ≤ 3 then 9 else 25))
#check (x 1 0 = 1 / 2 ∧ x 1 1 = 1 / 2 ∧ x 1 2 = 0 ∧ x 1 3 = 0 ∧ x 1 4 = 4 / 5 ∧
    r 1 0 = 0 ∧ r 1 1 = 1 / 3 ∧ r 1 2 = 1 / 3 ∧ r 1 3 = 1 / 5 ∧
    regret V 1 1 loss (1 / 2) policy 0 4 = 3 / 2 ∧ ‖x 1 4 - 0‖ ^ 2 = 16 / 25 ∧
    BanditRL.OnlineGradientDescent.project V (-1 / 2) = 0 ∧ (-1 / 2 : ℝ) ≠ 0)
#check (regret V 1 1 loss (1 / 2) policy 0 4 ≤ 59 / 10 ∧
    regret V 1 1 loss (1 / 2) policy 0 4 ≤ 15 / 2 ∧
    regret V (Real.sqrt 2 / 2) 1 loss (1 / 2) policy 0 4 ≤ Real.sqrt 50 ∧
    Real.sqrt 50 = Real.sqrt 2 * sInf {b : ℝ | ∃ η : ℝ, 0 < η ∧
      b = BanditRL.OnlineOptimalStep.upperBound 1 25 η})
#check (state V 1 1 loss (1 / 2) policy 2 = state V 1 1 futureLoss (1 / 2) policy 2 ∧
    loss 2 ≠ futureLoss 2 ∧ loss 1 = futureLoss 1)
#check ((∀ t : ℕ, output V 1 1 zeroLoss (1 / 2) zeroPolicy t = 1 / 2) ∧
    (∀ T : ℕ, energy V 1 1 zeroLoss (1 / 2) zeroPolicy T = 0) ∧
    regret V 1 1 zeroLoss (1 / 2) zeroPolicy 0 4 = 0 ∧
    ‖output V 1 1 zeroLoss (1 / 2) zeroPolicy 4 - 0‖ ^ 2 = 1 / 4 ∧
    regret V 1 1 zeroLoss (1 / 2) zeroPolicy 0 4 ≤ 0)
#check (output W 1 0 loss 0 policy 2 = 0 ∧ energy W 1 0 loss 0 policy 2 = 9 ∧
    selected W 1 0 loss 0 policy 1 = 3 ∧ regret W 1 0 loss 0 policy 0 2 = 0 ∧
    regret W 1 0 loss 0 policy 0 2 ≤ 0)
#check BanditRL.OnlineGradientDescent.project_unitInterval
#check BanditRL.OnlineConvex.convexExtended_iff_toReal
#check BanditRL.OnlineAdaptiveOSD.energy_eq_sum
#check BanditRL.OnlineAdaptiveOSD.output_succ
#check BanditRL.OnlineAdaptiveOSD.state_prefix
#check BanditRL.OnlineAdaptiveOSD.regret_bound
#check BanditRL.OnlineAdaptiveOSD.source_eq4_4
#check BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum
end AdaptiveProbe
