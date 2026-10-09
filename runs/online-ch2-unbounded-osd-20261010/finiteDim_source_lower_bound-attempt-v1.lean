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

namespace BanditRL.OnlineUnboundedOSDCanary
open BanditRL.OnlineUnboundedOSD

theorem finiteDim_source_lower_bound :
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
  classical
  have hv : ‖direction‖ = 1 := by simp [direction]
  have hx1 : vectorRun 64 1 = direction := by
    have hloss : (fun s z => (switchLoss 64 direction s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope 64 s • direction) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, real_inner_smul_left]
    unfold vectorRun
    rw [hloss, iterate_affine_prefix]
    norm_num [sum_range_succ, powerSteps, switchSlope]
  have hregular : ∀ t < 64, ConvexOn ℝ univ (switchLoss 64 direction t) ∧
      LipschitzWith 1 (switchLoss 64 direction t) := by
    intro t ht
    exact switching_loss_regular 64 direction hv t
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (7/5 : ℝ) < Real.sqrt 2 := by nlinarith
  have hh : (1/2 : ℝ) ^ (1/2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  have hphi_eq : phi (1/2) = Real.sqrt 2 - 4/3 := by
    unfold phi
    norm_num only [show 2 - (1/2 : ℝ) = 3/2 by norm_num,
      show 1 - (1/2 : ℝ) = 1/2 by norm_num]
    rw [hh]
    field_simp [ne_of_gt hspos]
    nlinarith [hsq]
  have hphi : (1/15 : ℝ) ≤ phi (1/2) := by rw [hphi_eq]; linarith
  have hp : 0 < phi (1/2) := (phi_range (1/2) (by norm_num) (by norm_num)).1
  have hthreshold : 2 / ((1 - (1/2 : ℝ)) * phi (1/2)) ≤ (64 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1 - 1/2) hp)).mpr
    nlinarith [hphi]
  have hprinted : (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤
      vectorRegret 64 :=
    switching_vector_lower_bound (1/2) (by norm_num) (by norm_num) 64 hthreshold direction hv
  have hpower : (64 : ℝ) ^ (2 - (1/2 : ℝ)) = 512 := by
    rw [show 2 - (1/2 : ℝ) = 1 + (1/2) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 64), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    norm_num
  have hlow : (256/15 : ℝ) ≤ vectorRegret 64 := by
    have hcompare : (256/15 : ℝ) ≤ (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) := by
      rw [hpower]
      linarith [hphi]
    exact hcompare.trans hprinted
  have hstrict : (17 : ℝ) < vectorRegret 64 :=
    lt_of_lt_of_le (by norm_num : (17 : ℝ) < 256/15) hlow
  have hex := theorem_5_4 (E := EuclideanSpace ℝ (Fin 2))
    (1/2) (by norm_num) (by norm_num) 64 hthreshold
  exact ⟨hv, hx1, hregular, hphi, hthreshold, hprinted, hlow, hstrict, hex⟩

end BanditRL.OnlineUnboundedOSDCanary
