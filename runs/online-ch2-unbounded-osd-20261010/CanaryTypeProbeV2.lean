import BanditRLProof.OnlineUnboundedOSD
noncomputable section
open Set Finset Filter Topology
open scoped InnerProductSpace
set_option autoImplicit false
namespace BanditRL.OnlineUnboundedOSDCanary
open BanditRL.OnlineUnboundedOSD
abbrev scalarRun (T t : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 t
abbrev scalarRegret (T : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 0 T
abbrev direction : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 0 1
abbrev vectorRun (T t : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T direction s z : EReal)) 0 t
abbrev vectorRegret (T : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T direction s z : EReal)) 0 0 T

#check (    powerSteps (1/2) 0 = 1 ∧
    0 < powerSteps (1/2) 1 ∧
    powerSteps (1/2) 1 < powerSteps (1/2) 0 ∧
    scalarRun 2 0 = 0 ∧ scalarRun 2 1 = 1 ∧
    scalarRun 2 2 = 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) ∧
    scalarRegret 2 = 1)
#check (    ‖direction‖ = 1 ∧ vectorRun 64 1 = direction ∧
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
          (powerSteps (1/2)) (fun t z => (loss t z : EReal)) 0 0 64))

end BanditRL.OnlineUnboundedOSDCanary
