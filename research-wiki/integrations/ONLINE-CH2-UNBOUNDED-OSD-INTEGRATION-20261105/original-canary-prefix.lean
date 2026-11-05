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
