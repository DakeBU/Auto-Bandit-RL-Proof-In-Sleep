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

theorem scalar_actual_two_rounds :
    powerSteps (1/2) 0 = 1 ∧
    0 < powerSteps (1/2) 1 ∧
    powerSteps (1/2) 1 < powerSteps (1/2) 0 ∧
    scalarRun 2 0 = 0 ∧ scalarRun 2 1 = 1 ∧
    scalarRun 2 2 = 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) ∧
    scalarRegret 2 = 1 := by
  classical
  have hin (a b : ℝ) : inner ℝ a b = b * a := rfl
  have hstate (t : ℕ) : scalarRun 2 t =
      -(∑ i ∈ range t, powerSteps (1/2) i * switchSlope 2 i) := by
    have hloss : (fun (s : ℕ) (z : ℝ) => (switchLoss 2 (1 : ℝ) s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope 2 s : ℝ) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, hin, mul_comm]
    unfold scalarRun
    rw [hloss, iterate_affine_prefix]
    simp
  have h0 : powerSteps (1/2) 0 = 1 := by norm_num [powerSteps]
  have hpos : 0 < powerSteps (1/2) 1 := powerSteps_pos (1/2) 1
  have hdec : powerSteps (1/2) 1 < powerSteps (1/2) 0 := by
    norm_num [powerSteps]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hx0 : scalarRun 2 0 = 0 := by simpa using hstate 0
  have hx1 : scalarRun 2 1 = 1 := by
    simpa [sum_range_succ, switchSlope, powerSteps] using hstate 1
  have hx2 : scalarRun 2 2 = 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) := by
    have h := hstate 2
    norm_num [sum_range_succ, switchSlope, powerSteps] at h
    linarith only [h]
  have hp : (2 : ℝ) ^ (1/2 : ℝ) = 2 * (2 : ℝ) ^ (-(1/2 : ℝ)) := by
    conv_lhs => rw [show (1/2 : ℝ) = 1 + (-(1/2 : ℝ)) by norm_num]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hr : scalarRegret 2 = 1 := by
    have h := switching_scalar_regret_identity (1/2) 2
    change scalarRegret 2 = _ at h
    norm_num [sum_range_succ, powerSteps] at h
    rw [hp] at h
    linarith only [h]
  exact ⟨h0, hpos, hdec, hx0, hx1, hx2, hr⟩

end BanditRL.OnlineUnboundedOSDCanary
