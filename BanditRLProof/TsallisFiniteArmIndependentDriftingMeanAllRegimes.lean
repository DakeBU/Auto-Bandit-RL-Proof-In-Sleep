import BanditRLProof.TsallisFiniteArmIndependentDriftingMeanRefinedRegret

/-!
# All-regimes regret for independent reward laws with drifting means

This module combines the compact-window refined endpoint with the logarithmic
fallback for the same independent, nonidentical generated reward law. The
comparator remains the fixed baseline arm `model.bestArm`.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- Total explicit fixed-comparator bound for independent nonidentical reward
laws with drifting means. The refined expression is used exactly inside its
coefficient-aware window; the logarithmic explicit-budget expression is used
on the complement. -/
noncomputable def finiteArmIndependentDriftingMeanAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (meanDeviation : Nat -> Fin K -> Real) : Real := by
  classical
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let scale := 2 * armCount * horizonMass
  let corruption :=
    finiteArmIndependentMeanDeviationBudget model horizon meanDeviation
  exact if actions.Nonempty ∧
      finiteArmIndependentDriftingMeanRefinedCorruptionWindow
        model horizon meanDeviation then
    1 + Real.log horizonMass +
      10 * Real.sqrt (corruption * reciprocalGap) *
        (2 + Real.sqrt
          (Real.log (scale / (corruption * reciprocalGap)) + 1))
  else
    (1 + Real.log horizonMass) * (1 + 25 * reciprocalGap) + corruption

/-- With one arm there is no suboptimal coordinate, so the all-regimes
envelope reduces to the logarithmic base term. -/
@[simp]
theorem finiteArmIndependentDriftingMeanAllRegimeBound_fin_one
    (model : FiniteBanditModel 1) (horizon : Nat)
    (meanDeviation : Nat -> Fin 1 -> Real) :
    finiteArmIndependentDriftingMeanAllRegimeBound
        model horizon meanDeviation =
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  have hbest : model.bestArm = 0 := Subsingleton.elim _ _
  simp [finiteArmIndependentDriftingMeanAllRegimeBound,
    finiteArmIndependentMeanDeviationBudget_eq, hbest]

/-- Generated scheduled half-Tsallis regret against the fixed baseline
comparator for every deterministic mean-deviation envelope and finite horizon.
The theorem automatically selects the compact-window refined branch or the
logarithmic fallback and requires no caller window proof. This is not dynamic
regret. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (meanDeviation : Nat -> Fin K -> Real)
    (hmeanDeviation : forall t arm,
      |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| <= meanDeviation t arm)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat) :
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
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      finiteArmIndependentDriftingMeanAllRegimeBound
        model horizon meanDeviation := by
  classical
  by_cases hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty
  · by_cases hwindow :
        finiteArmIndependentDriftingMeanRefinedCorruptionWindow
          model horizon meanDeviation
    · have hroute :=
        integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_refinedLocalExplicit_of_window
          model armLaw hprob hbound meanDeviation hmeanDeviation hsuboptimal
            hgapPos hgapLeOne horizon hwindow
      simpa only [finiteArmIndependentDriftingMeanAllRegimeBound,
        hsuboptimal, hwindow, and_self, if_pos] using hroute
    · have hroute :=
        integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_log
          model armLaw hprob hbound meanDeviation hmeanDeviation hgapPos horizon
      simpa only [finiteArmIndependentDriftingMeanAllRegimeBound,
        hsuboptimal, hwindow, and_false, if_neg] using hroute
  · have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_log
        model armLaw hprob hbound meanDeviation hmeanDeviation hgapPos horizon
    simpa only [finiteArmIndependentDriftingMeanAllRegimeBound,
      hsuboptimal, false_and, if_neg] using hroute

end Tsallis
end BanditRLProof
