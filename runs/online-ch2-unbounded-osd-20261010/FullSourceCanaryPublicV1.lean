import Tests.OnlineUnboundedOSDCanary
#check @BanditRL.OnlineUnboundedOSD.powerSteps
#print axioms BanditRL.OnlineUnboundedOSD.powerSteps
#check @BanditRL.OnlineUnboundedOSD.phi
#print axioms BanditRL.OnlineUnboundedOSD.phi
#check @BanditRL.OnlineUnboundedOSD.switchSlope
#print axioms BanditRL.OnlineUnboundedOSD.switchSlope
#check @BanditRL.OnlineUnboundedOSD.switchLoss
#print axioms BanditRL.OnlineUnboundedOSD.switchLoss
#check @BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
#print axioms BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
#check @BanditRL.OnlineUnboundedOSD.step_affine_fullSpace
#print axioms BanditRL.OnlineUnboundedOSD.step_affine_fullSpace
#check @BanditRL.OnlineUnboundedOSD.iterate_affine_prefix
#print axioms BanditRL.OnlineUnboundedOSD.iterate_affine_prefix
#check @BanditRL.OnlineUnboundedOSD.powerSteps_pos
#print axioms BanditRL.OnlineUnboundedOSD.powerSteps_pos
#check @BanditRL.OnlineUnboundedOSD.switching_loss_regular
#print axioms BanditRL.OnlineUnboundedOSD.switching_loss_regular
#check @BanditRL.OnlineUnboundedOSD.switching_scalar_regret_identity
#print axioms BanditRL.OnlineUnboundedOSD.switching_scalar_regret_identity
#check @BanditRL.OnlineUnboundedOSD.phi_range
#print axioms BanditRL.OnlineUnboundedOSD.phi_range
#check @BanditRL.OnlineUnboundedOSD.phi_limit
#print axioms BanditRL.OnlineUnboundedOSD.phi_limit
#check @BanditRL.OnlineUnboundedOSD.switching_scalar_lower_bound
#print axioms BanditRL.OnlineUnboundedOSD.switching_scalar_lower_bound
#check @BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound
#print axioms BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound
#check @BanditRL.OnlineUnboundedOSD.theorem_5_4
#print axioms BanditRL.OnlineUnboundedOSD.theorem_5_4
#check @BanditRL.OnlineUnboundedOSDCanary.scalar_actual_two_rounds
#print axioms BanditRL.OnlineUnboundedOSDCanary.scalar_actual_two_rounds
#check @BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound
#print axioms BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound

namespace BanditRL.OnlineUnboundedOSDCanary
open BanditRL.OnlineUnboundedOSD Set Finset
example :
    powerSteps (1/2) 0 = 1 ∧
    0 < powerSteps (1/2) 1 ∧
    powerSteps (1/2) 1 < powerSteps (1/2) 0 ∧
    scalarRun 2 0 = 0 ∧ scalarRun 2 1 = 1 ∧
    scalarRun 2 2 = 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) ∧
    scalarRegret 2 = 1 := by
  exact BanditRL.OnlineUnboundedOSDCanary.scalar_actual_two_rounds
example :
    ‖direction‖ = 1 ∧ vectorRun 64 1 = direction ∧
    (∀ t < 64, ConvexOn ℝ univ (switchLoss 64 direction t) ∧
      LipschitzWith 1 (switchLoss 64 direction t)) ∧
    (1/15 : ℝ) ≤ phi (1/2) ∧
    2 / ((1 - (1/2 : ℝ)) * phi (1/2)) ≤ (64 : ℝ) ∧
    (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤ vectorRegret 64 ∧
    (256/15 : ℝ) ≤ vectorRegret 64 ∧ (17 : ℝ) < vectorRegret 64 ∧
    (∃ loss : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ t < 64, ConvexOn ℝ univ (loss t) ∧ LipschitzWith 1 (loss t)) ∧
      (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤
        BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace
          (powerSteps (1/2)) (fun t z => (loss t z : EReal)) 0 0 64) := by
  exact BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound

end BanditRL.OnlineUnboundedOSDCanary
