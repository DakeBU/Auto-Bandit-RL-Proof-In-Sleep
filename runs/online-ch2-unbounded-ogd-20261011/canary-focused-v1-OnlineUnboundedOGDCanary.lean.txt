import BanditRLProof.OnlineUnboundedOGD
import Tests.OnlineUnboundedOSDCanary
import Mathlib.Tactic

noncomputable section
open Set Finset
open scoped InnerProductSpace
namespace UnboundedOGDProbe

abbrev eta : ℕ → ℝ := BanditRL.OnlineUnboundedOSD.powerSteps (1 / 2)
abbrev scalarLoss : ℕ → ℝ → ℝ := BanditRL.OnlineUnboundedOSD.switchLoss 2 (1 : ℝ)
abbrev scalarRun (t : ℕ) : ℝ :=
  BanditRL.OnlineGradientDescent.iterateVariable BanditRL.OnlineHuber.fullSpace eta scalarLoss 0 t
abbrev scalarRegret : ℝ :=
  BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace eta scalarLoss 0 0 2

theorem scalar_actual_two_rounds :
    eta 0 = 1 ∧ eta 1 = (2 : ℝ) ^ (-(1 / 2 : ℝ)) ∧
    0 < eta 1 ∧ eta 1 < eta 0 ∧
    (∀ z : ℝ, scalarLoss 0 z = -z ∧ scalarLoss 1 z = z) ∧
    (∀ t < 2, ConvexOn ℝ univ (scalarLoss t) ∧ LipschitzWith 1 (scalarLoss t) ∧
      Differentiable ℝ (scalarLoss t)) ∧
    (∀ z : ℝ, gradient (scalarLoss 0) z = -1 ∧ gradient (scalarLoss 1) z = 1) ∧
    scalarRun 0 = 0 ∧ scalarRun 1 = 1 ∧
    scalarRun 2 = 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ∧
    scalarRegret = 1 ∧
    (2 : ℝ) < 2 / ((1 - (1 / 2 : ℝ)) * BanditRL.OnlineUnboundedOSD.phi (1 / 2)) := by
  have hold := BanditRL.OnlineUnboundedOSDCanary.scalar_actual_two_rounds
  have hlinear (t : ℕ) : scalarLoss t =
      fun z => inner ℝ (BanditRL.OnlineUnboundedOSD.switchSlope 2 t • (1 : ℝ)) z := by
    funext z
    simp only [scalarLoss, BanditRL.OnlineUnboundedOSD.switchLoss, real_inner_smul_left]
  have hgrad (t : ℕ) (z : ℝ) : gradient (scalarLoss t) z =
      BanditRL.OnlineUnboundedOSD.switchSlope 2 t := by
    rw [hlinear]
    simpa using BanditRL.OnlineGradientDescentSource.gradient_linear
      (BanditRL.OnlineUnboundedOSD.switchSlope 2 t • (1 : ℝ)) z
  have hregular : ∀ t < 2, ConvexOn ℝ univ (scalarLoss t) ∧
      LipschitzWith 1 (scalarLoss t) ∧ Differentiable ℝ (scalarLoss t) := by
    intro t ht
    obtain ⟨hc, hl⟩ := BanditRL.OnlineUnboundedOSD.switching_loss_regular 2 (1 : ℝ) (by norm_num) t
    refine ⟨hc, hl, ?_⟩
    rw [hlinear]
    simpa only [InnerProductSpace.toDual_apply_apply] using
      (InnerProductSpace.toDual ℝ ℝ (BanditRL.OnlineUnboundedOSD.switchSlope 2 t • (1 : ℝ))).differentiable
  have hloss : ∀ z : ℝ, scalarLoss 0 z = -z ∧ scalarLoss 1 z = z := by
    intro z
    have hin (a b : ℝ) : inner ℝ a b = b * a := rfl
    norm_num [scalarLoss, BanditRL.OnlineUnboundedOSD.switchLoss,
      BanditRL.OnlineUnboundedOSD.switchSlope, hin]
  have h0 : scalarRun 0 = 0 := rfl
  have h1 : scalarRun 1 = 1 := by
    norm_num [scalarRun, BanditRL.OnlineGradientDescent.iterateVariable,
      BanditRL.OnlineGradientDescent.step, hgrad, BanditRL.OnlineHuber.project_fullSpace,
      eta, BanditRL.OnlineUnboundedOSD.powerSteps, BanditRL.OnlineUnboundedOSD.switchSlope]
  have h2 : scalarRun 2 = 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    norm_num [scalarRun, BanditRL.OnlineGradientDescent.iterateVariable,
      BanditRL.OnlineGradientDescent.step, hgrad, BanditRL.OnlineHuber.project_fullSpace,
      eta, BanditRL.OnlineUnboundedOSD.powerSteps, BanditRL.OnlineUnboundedOSD.switchSlope]
  have hr : scalarRegret = 1 := by
    change (∑ t ∈ range 2, (scalarLoss t (scalarRun t) - scalarLoss t 0)) = 1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, h0, h1, (hloss 0).1, (hloss 0).2, (hloss 1).2]
    norm_num
  have hp := BanditRL.OnlineUnboundedOSD.phi_range (1 / 2) (by norm_num) (by norm_num)
  have hbelow : (2 : ℝ) < 2 / ((1 - (1 / 2 : ℝ)) * BanditRL.OnlineUnboundedOSD.phi (1 / 2)) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1 - 1 / 2) hp.1)).mpr
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [hp.2]
  refine ⟨hold.1, ?_, hold.2.1, hold.2.2.1, hloss, hregular, ?_, h0, h1, h2, hr, hbelow⟩
  · norm_num [eta, BanditRL.OnlineUnboundedOSD.powerSteps]
  · intro z
    norm_num [hgrad, BanditRL.OnlineUnboundedOSD.switchSlope]

theorem finiteDim_terminal_lower_bound :
    (1 / 15 : ℝ) ≤ BanditRL.OnlineUnboundedOSD.phi (1 / 2) ∧
    2 / ((1 - (1 / 2 : ℝ)) * BanditRL.OnlineUnboundedOSD.phi (1 / 2)) ≤ (64 : ℝ) ∧
    (64 : ℝ) ^ (2 - (1 / 2 : ℝ)) = 512 ∧
    (∃ loss : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ t < 64, ConvexOn ℝ univ (loss t) ∧ LipschitzWith 1 (loss t) ∧
        Differentiable ℝ (loss t)) ∧
      (1 / 2 : ℝ) * BanditRL.OnlineUnboundedOSD.phi (1 / 2) *
          (64 : ℝ) ^ (2 - (1 / 2 : ℝ)) ≤
        BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace eta loss 0 0 64 ∧
      (256 / 15 : ℝ) ≤
        BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace eta loss 0 0 64 ∧
      (17 : ℝ) <
        BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace eta loss 0 0 64) := by
  have old := BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound
  have hphi : (1 / 15 : ℝ) ≤ BanditRL.OnlineUnboundedOSD.phi (1 / 2) := old.2.2.2.1
  have hthreshold : 2 / ((1 - (1 / 2 : ℝ)) * BanditRL.OnlineUnboundedOSD.phi (1 / 2)) ≤ (64 : ℝ) :=
    old.2.2.2.2.1
  have hpower : (64 : ℝ) ^ (2 - (1 / 2 : ℝ)) = 512 := by
    rw [show 2 - (1 / 2 : ℝ) = 1 + (1 / 2) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 64), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    norm_num
  obtain ⟨loss, hregular, hprinted⟩ := BanditRL.OnlineUnboundedOGD.regret_lower_bound
    (E := EuclideanSpace ℝ (Fin 2)) (1 / 2) (by norm_num) (by norm_num) 64 hthreshold
  have hlow : (256 / 15 : ℝ) ≤
      BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace eta loss 0 0 64 := by
    have hc : (256 / 15 : ℝ) ≤ (1 / 2 : ℝ) * BanditRL.OnlineUnboundedOSD.phi (1 / 2) *
        (64 : ℝ) ^ (2 - (1 / 2 : ℝ)) := by
      rw [hpower]
      linarith [hphi]
    exact hc.trans hprinted
  have hstrict : (17 : ℝ) <
      BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace eta loss 0 0 64 :=
    lt_of_lt_of_le (by norm_num : (17 : ℝ) < 256 / 15) hlow
  exact ⟨hphi, hthreshold, hpower, loss, hregular, hprinted, hlow, hstrict⟩

end UnboundedOGDProbe
