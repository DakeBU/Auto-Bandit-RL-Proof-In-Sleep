import BanditRLProof.OnlineUnboundedOSD
import BanditRLProof.OnlineGradientDescentSource
import Mathlib.Tactic

noncomputable section
open Set Finset
open scoped InnerProductSpace
namespace BanditRL.OnlineUnboundedOGD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem regret_lower_bound [Nontrivial E] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * BanditRL.OnlineUnboundedOSD.phi α) ≤ (T : ℝ)) :
    ∃ loss : ℕ → E → ℝ,
      (∀ t < T, ConvexOn ℝ univ (loss t) ∧ LipschitzWith 1 (loss t) ∧
        Differentiable ℝ (loss t)) ∧
      (1 / 2 : ℝ) * BanditRL.OnlineUnboundedOSD.phi α * (T : ℝ) ^ (2 - α) ≤
        BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace
          (BanditRL.OnlineUnboundedOSD.powerSteps α) loss 0 0 T := by
  obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  let loss : ℕ → E → ℝ := BanditRL.OnlineUnboundedOSD.switchLoss T v
  let η : ℕ → ℝ := BanditRL.OnlineUnboundedOSD.powerSteps α
  have hlinear (t : ℕ) : loss t =
      fun z => inner ℝ (BanditRL.OnlineUnboundedOSD.switchSlope T t • v) z := by
    funext z
    simp only [loss, BanditRL.OnlineUnboundedOSD.switchLoss, real_inner_smul_left]
  have hgradient (t : ℕ) (z : E) : gradient (loss t) z =
      BanditRL.OnlineUnboundedOSD.switchSlope T t • v := by
    rw [hlinear]
    exact BanditRL.OnlineGradientDescentSource.gradient_linear _ _
  have hsupport (t : ℕ) (z : E) :
      BanditRL.OnlineSubgradientDescent.currentSubgradient
        (fun y => (loss t y : EReal)) z = BanditRL.OnlineUnboundedOSD.switchSlope T t • v := by
    have hf : (fun y => (loss t y : EReal)) =
        fun y => ((inner ℝ (BanditRL.OnlineUnboundedOSD.switchSlope T t • v) y + 0 : ℝ) : EReal) := by
      funext y
      rw [hlinear]
      simp
    rw [hf]
    exact BanditRL.OnlineUnboundedOSD.currentSubgradient_affine _ _ _
  have htrajectory (t : ℕ) :
      BanditRL.OnlineGradientDescent.iterateVariable BanditRL.OnlineHuber.fullSpace η loss 0 t =
      BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace η
        (fun s z => (loss s z : EReal)) 0 t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [BanditRL.OnlineGradientDescent.iterateVariable,
        BanditRL.OnlineSubgradientDescent.iterate, BanditRL.OnlineGradientDescent.step,
        BanditRL.OnlineSubgradientDescent.step, hgradient, hsupport, ih]
  have hregret :
      BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace η loss 0 0 T =
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace η
        (fun s z => (loss s z : EReal)) 0 0 T := by
    unfold BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineSubgradientDescent.regret
    simp only [htrajectory, EReal.toReal_coe]
  refine ⟨loss, ?_, ?_⟩
  · intro t ht
    obtain ⟨hc, hl⟩ := BanditRL.OnlineUnboundedOSD.switching_loss_regular T v hv t
    refine ⟨hc, hl, ?_⟩
    rw [hlinear]
    simpa only [InnerProductSpace.toDual_apply_apply] using
      (InnerProductSpace.toDual ℝ E (BanditRL.OnlineUnboundedOSD.switchSlope T t • v)).differentiable
  · change (1 / 2 : ℝ) * BanditRL.OnlineUnboundedOSD.phi α * (T : ℝ) ^ (2 - α) ≤
      BanditRL.OnlineGradientDescent.regretVariable BanditRL.OnlineHuber.fullSpace η loss 0 0 T
    rw [hregret]
    exact BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound α hα0 hα1 T hT v hv

end BanditRL.OnlineUnboundedOGD
