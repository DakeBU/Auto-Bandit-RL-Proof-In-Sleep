import BanditRLProof.TsallisScheduledIIDMeanGap
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite-arm IID reward-law producer for scheduled half-Tsallis regret

This module turns one probability law per rational-valued arm into a finite
product reward-vector law.  Rewards are clipped pointwise before conversion to
losses so that the abstract IID loss-state API has global `[0, 1]` bounds; an
almost-sure `[0, 1]` arm-law contract then proves that clipping does not change
the coordinate means or the finite-bandit gaps.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

/-- Pointwise projection of a rational reward into the real unit interval. -/
noncomputable def clippedUnitReward (reward : Rat) : Real :=
  max 0 (min 1 ((reward : Rat) : Real))

theorem clippedUnitReward_nonneg (reward : Rat) :
    0 <= clippedUnitReward reward := by
  exact le_max_left _ _

theorem clippedUnitReward_le_one (reward : Rat) :
    clippedUnitReward reward <= 1 := by
  exact max_le zero_le_one (min_le_left _ _)

theorem clippedUnitReward_eq_of_mem_Icc (reward : Rat)
    (hreward : ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1) :
    clippedUnitReward reward = ((reward : Rat) : Real) := by
  rw [clippedUnitReward, min_eq_right hreward.2, max_eq_right hreward.1]

theorem measurable_clippedUnitReward : Measurable clippedUnitReward := by
  exact measurable_of_countable _

/-- The independent one-round reward vector induced by one law per arm. -/
noncomputable def finiteArmIIDRewardVectorLaw {K : Nat}
    (armLaw : Fin K -> Measure Rat) : Measure (Fin K -> Rat) :=
  Measure.pi armLaw

/-- Convert a sampled reward vector into the selected arm's clipped loss. -/
noncomputable def finiteArmIIDRewardVectorLoss {K : Nat}
    (state : Fin K -> Rat) (arm : Fin K) : Real :=
  1 - clippedUnitReward (state arm)

theorem measurable_finiteArmIIDRewardVectorLoss {K : Nat} :
    Measurable (fun input : (Fin K -> Rat) × Fin K =>
      finiteArmIIDRewardVectorLoss input.1 input.2) := by
  exact measurable_of_countable _

theorem finiteArmIIDRewardVectorLoss_nonneg {K : Nat}
    (state : Fin K -> Rat) (arm : Fin K) :
    0 <= finiteArmIIDRewardVectorLoss state arm := by
  dsimp only [finiteArmIIDRewardVectorLoss]
  linarith [clippedUnitReward_le_one (state arm)]

theorem finiteArmIIDRewardVectorLoss_le_one {K : Nat}
    (state : Fin K -> Rat) (arm : Fin K) :
    finiteArmIIDRewardVectorLoss state arm <= 1 := by
  dsimp only [finiteArmIIDRewardVectorLoss]
  linarith [clippedUnitReward_nonneg (state arm)]

theorem integrable_clippedUnitReward (mu : Measure Rat)
    [IsFiniteMeasure mu] : Integrable clippedUnitReward mu := by
  refine Integrable.of_bound measurable_clippedUnitReward.aestronglyMeasurable 1 ?_
  filter_upwards [] with reward
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [clippedUnitReward_nonneg reward],
    clippedUnitReward_le_one reward⟩

/-- Under an almost-sure unit-interval contract, the product-coordinate
clipped reward has exactly the supplied finite-bandit mean. -/
theorem integral_finiteArmIIDRewardVectorLaw_clippedUnitReward_eq_mean
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (arm : Fin K) :
    integral (finiteArmIIDRewardVectorLaw armLaw)
        (fun state => clippedUnitReward (state arm)) =
      ((model.mean arm : Rat) : Real) := by
  letI (i : Fin K) : IsProbabilityMeasure (armLaw i) := hprob i
  rw [finiteArmIIDRewardVectorLaw,
    MeasureTheory.integral_comp_eval
      (integrable_clippedUnitReward (armLaw arm)).aestronglyMeasurable]
  calc
    integral (armLaw arm) clippedUnitReward =
        integral (armLaw arm) (fun reward : Rat =>
          ((reward : Rat) : Real)) := by
      apply integral_congr_ae
      filter_upwards [hbound arm] with reward hreward
      exact clippedUnitReward_eq_of_mem_Icc reward hreward
    _ = ((model.mean arm : Rat) : Real) := hmean arm

/-- The one-round IID loss-state mean gap is exactly the rational finite-bandit
model gap after coercion to the reals. -/
theorem iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (arm : Fin K) :
    iidLossStateMeanGap (finiteArmIIDRewardVectorLaw armLaw)
        finiteArmIIDRewardVectorLoss model.bestArm arm =
      ((model.gap arm : Rat) : Real) := by
  letI (i : Fin K) : IsProbabilityMeasure (armLaw i) := hprob i
  have hbestIntegrable : Integrable
      (fun state : Fin K -> Rat => clippedUnitReward (state model.bestArm))
      (finiteArmIIDRewardVectorLaw armLaw) := by
    exact MeasureTheory.integrable_comp_eval
      (integrable_clippedUnitReward (armLaw model.bestArm))
  have harmIntegrable : Integrable
      (fun state : Fin K -> Rat => clippedUnitReward (state arm))
      (finiteArmIIDRewardVectorLaw armLaw) := by
    exact MeasureTheory.integrable_comp_eval
      (integrable_clippedUnitReward (armLaw arm))
  rw [iidLossStateMeanGap]
  calc
    integral (finiteArmIIDRewardVectorLaw armLaw)
        (fun state => finiteArmIIDRewardVectorLoss state arm -
          finiteArmIIDRewardVectorLoss state model.bestArm) =
        integral (finiteArmIIDRewardVectorLaw armLaw)
          (fun state => clippedUnitReward (state model.bestArm) -
            clippedUnitReward (state arm)) := by
      congr 1
      funext state
      simp only [finiteArmIIDRewardVectorLoss]
      ring
    _ = integral (finiteArmIIDRewardVectorLaw armLaw)
          (fun state => clippedUnitReward (state model.bestArm)) -
        integral (finiteArmIIDRewardVectorLaw armLaw)
          (fun state => clippedUnitReward (state arm)) :=
      integral_sub hbestIntegrable harmIntegrable
    _ = ((model.mean model.bestArm : Rat) : Real) -
        ((model.mean arm : Rat) : Real) := by
      rw [integral_finiteArmIIDRewardVectorLaw_clippedUnitReward_eq_mean
          model armLaw hprob hbound hmean model.bestArm,
        integral_finiteArmIIDRewardVectorLaw_clippedUnitReward_eq_mean
          model armLaw hprob hbound hmean arm]
    _ = ((model.gap arm : Rat) : Real) := by
      by_cases h : arm = model.bestArm
      · simp [h]
      · simp [FiniteBanditModel.gap, FiniteBanditModel.bestMean, h]

/-- A finite collection of bounded rational reward laws supplies the concrete
IID stochastic model for the generated scheduled half-Tsallis logarithmic
regret theorem.  The latent one-round law is the independent product of arm
laws, while the observed feedback is the selected clipped loss. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDRewardLawRegret_le_log
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (horizon : Nat) (corruption : Real) (hcorruption : 0 <= corruption) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIIDRewardVectorLaw armLaw
    let loss := iidLossStatePredictableLossVector
      finiteArmIIDRewardVectorLoss measurable_finiteArmIIDRewardVectorLoss
      finiteArmIIDRewardVectorLoss_nonneg finiteArmIIDRewardVectorLoss_le_one
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) + corruption := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (arm : Fin K) : IsProbabilityMeasure (armLaw arm) := hprob arm
  letI : IsProbabilityMeasure (finiteArmIIDRewardVectorLaw armLaw) := by
    rw [finiteArmIIDRewardVectorLaw]
    infer_instance
  dsimp only
  simpa only [
      iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap
        model armLaw hprob hbound hmean] using
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_iidLossState
      (finiteArmIIDRewardVectorLaw armLaw) finiteArmIIDRewardVectorLoss
      measurable_finiteArmIIDRewardVectorLoss
      finiteArmIIDRewardVectorLoss_nonneg finiteArmIIDRewardVectorLoss_le_one
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      (Finset.mem_univ model.bestArm) horizon
      (fun arm harm => by
        rw [iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap
          model armLaw hprob hbound hmean]
        exact hgapPos arm (Finset.ne_of_mem_erase harm))
      corruption hcorruption

end Tsallis
end BanditRLProof
