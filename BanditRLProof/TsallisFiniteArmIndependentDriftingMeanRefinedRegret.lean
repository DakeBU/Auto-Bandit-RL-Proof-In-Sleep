import BanditRLProof.TsallisFiniteArmIndependentDriftingMeanRewardLaw
import BanditRLProof.TsallisSqrtScheduleSelfBoundingRefinedTuning
import BanditRLProof.TsallisSqrtScheduleSelfBoundingRefinedWindow

/-!
# Refined regret for independent reward laws with drifting means

This module connects the explicit mean-deviation budget of independent,
nonidentical finite-arm reward laws to the compiled refined local
self-bounding optimizer.  The comparator remains the fixed baseline arm
`model.bestArm`.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- The coefficient-aware refined corruption window specialized to the
explicit mean-deviation budget. -/
noncomputable def finiteArmIndependentDriftingMeanRefinedCorruptionWindow
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (meanDeviation : Nat -> Fin K -> Real) : Prop :=
  RefinedLocalCorruptionWindow
    (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real)
    (((horizon + 1 : Nat) : Real))
    (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
      (fun arm => 1 / ((model.gap arm : Rat) : Real)))
    (finiteArmIndependentMeanDeviationBudget model horizon meanDeviation)

/-- Refined local square-root regret against the fixed baseline comparator
for independent, nonidentical reward laws whose means drift within an explicit
armwise envelope.  This is not dynamic regret. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_refinedLocalExplicit_of_window
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (meanDeviation : Nat -> Fin K -> Real)
    (hmeanDeviation : forall t arm,
      |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| <= meanDeviation t arm)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat)
    (hwindow : finiteArmIndependentDriftingMeanRefinedCorruptionWindow
      model horizon meanDeviation) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIndependentRewardVectorLaw armLaw
    let value := fun _ : Nat => finiteArmIIDRewardVectorLoss
    let loss := iidTimeVaryingLossStatePredictableLossVector value
      (fun _ => measurable_finiteArmIIDRewardVectorLoss)
      (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
      (fun _ => finiteArmIIDRewardVectorLoss_le_one)
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi law
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    let reciprocalGap :=
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
        (fun arm => 1 / ((model.gap arm : Rat) : Real))
    let horizonMass : Real := ((horizon + 1 : Nat) : Real)
    let scale :=
      2 * (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
        horizonMass
    let corruption :=
      finiteArmIndependentMeanDeviationBudget model horizon meanDeviation
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      1 + Real.log horizonMass +
        10 * Real.sqrt (corruption * reciprocalGap) *
          (2 + Real.sqrt
            (Real.log (scale / (corruption * reciprocalGap)) + 1)) := by
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let corruption :=
    finiteArmIndependentMeanDeviationBudget model horizon meanDeviation
  have harmCount : 1 <= armCount := by
    dsimp [armCount, actions]
    exact_mod_cast hsuboptimal.card_pos
  have hhorizonMass : 0 < horizonMass := by
    dsimp [horizonMass]
    positivity
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap, actions]
    exact sum_inv_pos_of_nonempty
      ((Finset.univ : Finset (Fin K)).erase model.bestArm)
        hsuboptimal (fun arm => ((model.gap arm : Rat) : Real))
        (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
  have hcountGap : armCount <= reciprocalGap := by
    calc
      armCount = actions.sum (fun _ => (1 : Real)) := by
        simp [armCount]
      _ <= actions.sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real)) := by
        apply Finset.sum_le_sum
        intro arm harm
        have hpos := hgapPos arm (Finset.ne_of_mem_erase harm)
        rw [le_div_iff₀ hpos]
        simpa using hgapLeOne arm (Finset.ne_of_mem_erase harm)
      _ = reciprocalGap := by rfl
  have hwindow' : RefinedLocalCorruptionWindow
      armCount horizonMass reciprocalGap corruption := by
    simpa only [finiteArmIndependentDriftingMeanRefinedCorruptionWindow,
      armCount, horizonMass, reciprocalGap, corruption, actions] using hwindow
  have hbounds := refinedLocalCorruptionWindow_scalar_bounds
    armCount horizonMass reciprocalGap corruption harmCount hhorizonMass
      hreciprocalGap hcountGap hwindow'
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (t : Nat) (arm : Fin K) :
      IsProbabilityMeasure (armLaw t arm) := hprob t arm
  letI (t : Nat) :
      IsProbabilityMeasure (finiteArmIndependentRewardVectorLaw armLaw t) := by
    rw [finiteArmIndependentRewardVectorLaw, finiteArmIIDRewardVectorLaw]
    infer_instance
  let value : Nat -> (Fin K -> Rat) -> Fin K -> Real :=
    fun _ => finiteArmIIDRewardVectorLoss
  let loss := iidTimeVaryingLossStatePredictableLossVector value
    (fun _ => measurable_finiteArmIIDRewardVectorLoss)
    (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
    (fun _ => finiteArmIIDRewardVectorLoss_le_one)
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let prior := Measure.infinitePi
    (finiteArmIndependentRewardVectorLaw armLaw)
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
  have hselfBounding :=
    integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLaw_hasSelfBounding
      model armLaw hprob hbound meanDeviation hmeanDeviation horizon
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedLocalExplicit
      prior arms harms loss (Finset.mem_univ model.bestArm) horizon baseGap
        (by simpa only [arms] using hsuboptimal)
        (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
        corruption hbounds.2.2.2.2 hbounds.1 hbounds.2.1
        hbounds.2.2.1 hbounds.2.2.2.1
        (by simpa only [value, loss, arms, harms, selector, prior, mu, baseGap,
          corruption] using hselfBounding)
  simpa only [value, loss, arms, harms, selector, prior, mu, baseGap,
    corruption, reciprocalGap, horizonMass, actions, armCount] using hroute

end Tsallis
end BanditRLProof
