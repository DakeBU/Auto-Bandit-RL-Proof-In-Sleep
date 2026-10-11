import Tests.OnlineAdaptiveOSDCanary
noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineAdaptiveOSD AdaptiveProbe

example (U : Domain (E := ℝ)) (t : ℕ) :
    IsConvexExtended (loss t) ∧
    BanditRL.OnlineSubgradientDescent.SubdifferentiableOn U (loss t) ∧
    ∀ z : ℝ, feedback t ∈ SourceSubdifferential (loss t) z := by
  exact AdaptiveProbe.loss_regular U t
#check AdaptiveProbe.loss_regular
#print axioms AdaptiveProbe.loss_regular

example :
    (∀ α : ℝ, ∀ t : ℕ, selected V α 1 loss (1 / 2) policy t = feedback t) ∧
    (∀ α : ℝ, ∀ T : ℕ, T ≤ 4 →
      q α T = if T ≤ 1 then 0 else if T ≤ 3 then 9 else 25) := by
  exact AdaptiveProbe.feedback_energy
#check AdaptiveProbe.feedback_energy
#print axioms AdaptiveProbe.feedback_energy

example :
    x 1 0 = 1 / 2 ∧ x 1 1 = 1 / 2 ∧ x 1 2 = 0 ∧ x 1 3 = 0 ∧ x 1 4 = 4 / 5 ∧
    r 1 0 = 0 ∧ r 1 1 = 1 / 3 ∧ r 1 2 = 1 / 3 ∧ r 1 3 = 1 / 5 ∧
    regret V 1 1 loss (1 / 2) policy 0 4 = 3 / 2 ∧ ‖x 1 4 - 0‖ ^ 2 = 16 / 25 ∧
    BanditRL.OnlineGradientDescent.project V (-1 / 2) = 0 ∧ (-1 / 2 : ℝ) ≠ 0 := by
  exact AdaptiveProbe.trace_canary
#check AdaptiveProbe.trace_canary
#print axioms AdaptiveProbe.trace_canary

example :
    regret V 1 1 loss (1 / 2) policy 0 4 ≤ 59 / 10 ∧
    regret V 1 1 loss (1 / 2) policy 0 4 ≤ 15 / 2 ∧
    regret V (Real.sqrt 2 / 2) 1 loss (1 / 2) policy 0 4 ≤ Real.sqrt 50 ∧
    Real.sqrt 50 = Real.sqrt 2 * sInf {b : ℝ | ∃ η : ℝ, 0 < η ∧
      b = BanditRL.OnlineOptimalStep.upperBound 1 25 η} := by
  exact AdaptiveProbe.performance_canary
#check AdaptiveProbe.performance_canary
#print axioms AdaptiveProbe.performance_canary

example :
    state V 1 1 loss (1 / 2) policy 2 = state V 1 1 futureLoss (1 / 2) policy 2 ∧
    loss 2 ≠ futureLoss 2 ∧ loss 1 = futureLoss 1 := by
  exact AdaptiveProbe.prefix_canary
#check AdaptiveProbe.prefix_canary
#print axioms AdaptiveProbe.prefix_canary

example :
    (∀ t : ℕ, output V 1 1 zeroLoss (1 / 2) zeroPolicy t = 1 / 2) ∧
    (∀ T : ℕ, energy V 1 1 zeroLoss (1 / 2) zeroPolicy T = 0) ∧
    regret V 1 1 zeroLoss (1 / 2) zeroPolicy 0 4 = 0 ∧
    ‖output V 1 1 zeroLoss (1 / 2) zeroPolicy 4 - 0‖ ^ 2 = 1 / 4 ∧
    regret V 1 1 zeroLoss (1 / 2) zeroPolicy 0 4 ≤ 0 := by
  exact AdaptiveProbe.zero_energy_canary
#check AdaptiveProbe.zero_energy_canary
#print axioms AdaptiveProbe.zero_energy_canary

example :
    output W 1 0 loss 0 policy 2 = 0 ∧ energy W 1 0 loss 0 policy 2 = 9 ∧
    selected W 1 0 loss 0 policy 1 = 3 ∧ regret W 1 0 loss 0 policy 0 2 = 0 ∧
    regret W 1 0 loss 0 policy 0 2 ≤ 0 := by
  exact AdaptiveProbe.zero_diameter_canary
#check AdaptiveProbe.zero_diameter_canary
#print axioms AdaptiveProbe.zero_diameter_canary
