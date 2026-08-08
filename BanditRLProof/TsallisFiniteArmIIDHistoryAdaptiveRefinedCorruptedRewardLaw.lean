import BanditRLProof.TsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLaw
import BanditRLProof.TsallisSqrtScheduleSelfBoundingRefinedTuning
import BanditRLProof.TsallisSqrtScheduleSelfBoundingRefinedWindow

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- The history-adaptive finite-arm corruption model supplies the terminal
self-bounding contract consumed by the refined square-root schedule route. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLaw_hasSelfBounding
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIIDRewardVectorLaw armLaw
    let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
    (Finset.range (horizon + 1)).sum (fun t =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum (fun arm =>
          baseGap arm * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
              sampledScheduledHalfTsallisSqrtSchedule t arm)) -
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon source <=
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
          sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass model.bestArm) horizon) := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (arm : Fin K) : IsProbabilityMeasure (armLaw arm) := hprob arm
  let law := finiteArmIIDRewardVectorLaw armLaw
  letI : IsProbabilityMeasure law := by
    dsimp only [law, finiteArmIIDRewardVectorLaw]
    infer_instance
  let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
  let referenceLoss := iidLossStatePredictableLossVector
    (finiteArmIIDRewardVectorLoss (K := K))
    (measurable_finiteArmIIDRewardVectorLoss (K := K))
    (finiteArmIIDRewardVectorLoss_nonneg (K := K))
    (finiteArmIIDRewardVectorLoss_le_one (K := K))
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms eta loss
  let prior := Measure.infinitePi (fun _ : Nat => law)
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let mu := prior ⊗ₘ trajectoryKernel
  let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
  let deviation := fun (t : Nat) (arm : Fin K) =>
    source.envelope t arm + source.envelope t model.bestArm
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, eta, loss] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveTrajectoryKernel
        source arms harms eta selector.finiteHistory horizon
  have hindependent : HasScheduledIndependentMeanGapLaw
      mu arms referenceLoss model.bestArm
        (iidLossStateMeanGap law finiteArmIIDRewardVectorLoss model.bestArm)
      horizon := by
    simpa only [mu, prior, trajectoryKernel, referenceLoss, law] using
      hasScheduledIndependentMeanGapLaw_of_iidLossState
        law finiteArmIIDRewardVectorLoss
          measurable_finiteArmIIDRewardVectorLoss
          finiteArmIIDRewardVectorLoss_nonneg
          finiteArmIIDRewardVectorLoss_le_one
          arms model.bestArm horizon trajectoryKernel hfactor
  have hreferenceRaw : HasScheduledExpectedGapLaw
      mu arms harms eta referenceLoss model.bestArm
        (iidLossStateMeanGap law finiteArmIIDRewardVectorLoss model.bestArm)
      horizon :=
    hasScheduledExpectedGapLaw_of_independentMeanGapLaw
      mu arms harms eta referenceLoss model.bestArm
        (iidLossStateMeanGap law finiteArmIIDRewardVectorLoss model.bestArm)
        horizon hindependent
  have hgapEq : forall arm,
      iidLossStateMeanGap law finiteArmIIDRewardVectorLoss
          model.bestArm arm = baseGap arm := by
    intro arm
    simpa only [law, baseGap] using
      iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap
        model armLaw hprob hbound hmean arm
  have hreferenceGapLaw : HasScheduledExpectedGapLaw
      mu arms harms eta referenceLoss model.bestArm baseGap horizon := by
    intro t ht arm harm
    simpa only [hgapEq arm] using hreferenceRaw t ht arm harm
  have hdeviation : forall t, t <= horizon -> forall sample arm,
      arm ∈ arms.erase model.bestArm ->
      |(Exp3.predictableLossAt loss t sample arm -
            Exp3.predictableLossAt loss t sample model.bestArm) -
          (Exp3.predictableLossAt referenceLoss t sample arm -
            Exp3.predictableLossAt referenceLoss t sample model.bestArm)| <=
        deviation t arm := by
    intro t _ht sample arm _harm
    simpa only [loss, referenceLoss, deviation] using
      abs_historyAdaptiveCorruptedPredictableLossDiff_sub_baseLossDiff_le
        source t sample model.bestArm arm
  have hselfBounding :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase model.bestArm).sum (fun arm =>
            baseGap arm * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t arm)) -
        scheduledTimeVaryingGapDeviationBudget
          arms model.bestArm horizon deviation <=
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass model.bestArm) horizon) :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_referenceExpectedGapLaw
      mu arms harms eta loss referenceLoss (Finset.mem_univ model.bestArm)
      baseGap deviation horizon hreferenceGapLaw hdeviation
  simpa only [arms, harms, eta, selector, prior, trajectoryKernel, mu, loss,
    baseGap, deviation, finiteArmIIDHistoryAdaptiveRewardCorruptionBudget] using
      hselfBounding

/-- Refined local square-root corruption regret for the concrete finite-arm IID
history-adaptive reward-shift model. The corruption scalar is the source's
deterministic envelope budget, rather than a free theorem parameter. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (horizon : Nat)
    (hcorruption :
      0 < finiteArmIIDHistoryAdaptiveRewardCorruptionBudget
        model horizon source)
    (hscalarLower :
      2 <=
        (2 * (((Finset.univ : Finset (Fin K)).erase
            model.bestArm).card : Real) * (((horizon + 1 : Nat) : Real))) /
          (25 * (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real))) ^ 2))
    (hscalarThresholdOne :
      (2 * (((Finset.univ : Finset (Fin K)).erase
            model.bestArm).card : Real) * (((horizon + 1 : Nat) : Real))) /
          (25 * (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real))) ^ 2) <=
        2 * (((horizon + 1 : Nat) : Real)))
    (hcorruptionUpper :
      2 * (finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon source *
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) <=
        2 * (((Finset.univ : Finset (Fin K)).erase
          model.bestArm).card : Real) * (((horizon + 1 : Nat) : Real)))
    (hcorruptionLower :
      25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real)) *
        (Real.log
            ((2 * (((Finset.univ : Finset (Fin K)).erase
                model.bestArm).card : Real) *
                (((horizon + 1 : Nat) : Real))) /
              (25 * (((Finset.univ : Finset (Fin K)).erase
                model.bestArm).sum
                  (fun arm => 1 / ((model.gap arm : Rat) : Real))) ^ 2)) + 2) <=
          finiteArmIIDHistoryAdaptiveRewardCorruptionBudget
            model horizon source) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIIDRewardVectorLaw armLaw
    let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
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
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon source
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      1 + Real.log horizonMass +
        10 * Real.sqrt (corruption * reciprocalGap) *
          (2 + Real.sqrt
            (Real.log (scale / (corruption * reciprocalGap)) + 1)) := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (arm : Fin K) : IsProbabilityMeasure (armLaw arm) := hprob arm
  let law := finiteArmIIDRewardVectorLaw armLaw
  letI : IsProbabilityMeasure law := by
    dsimp only [law, finiteArmIIDRewardVectorLaw]
    infer_instance
  let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let prior := Measure.infinitePi (fun _ : Nat => law)
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
  let corruption :=
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon source
  have hselfBounding :=
    integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLaw_hasSelfBounding
      model armLaw hprob hbound hmean source horizon
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedLocalExplicit
      prior arms harms loss (Finset.mem_univ model.bestArm) horizon baseGap
        (by simpa only [arms] using hsuboptimal)
        (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
        corruption hcorruption
        (by simpa only [arms, baseGap] using hscalarLower)
        (by simpa only [arms, baseGap] using hscalarThresholdOne)
        (by simpa only [arms, baseGap, corruption] using hcorruptionUpper)
        (by simpa only [arms, baseGap, corruption] using hcorruptionLower)
        (by simpa only [law, loss, arms, harms, selector, prior, mu, baseGap,
          corruption] using hselfBounding)
  simpa only [law, loss, arms, harms, selector, prior, mu, baseGap, corruption]
    using hroute

/-- The coefficient-aware refined corruption window specialized to the
finite-arm IID history-adaptive reward-shift model. -/
noncomputable def finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K) : Prop :=
  RefinedLocalCorruptionWindow
    (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real)
    (((horizon + 1 : Nat) : Real))
    (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
      (fun arm => 1 / ((model.gap arm : Rat) : Real)))
    (finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon source)

/-- A model-facing refined theorem with the low-level scalar inequalities
replaced by a compact corruption window. Unit-bounded positive model gaps imply
that the reciprocal-gap sum dominates the number of suboptimal arms. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat)
    (hwindow : finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow
      model horizon source) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIIDRewardVectorLaw armLaw
    let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
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
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon source
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
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon source
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
    simpa only [finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow,
      armCount, horizonMass, reciprocalGap, corruption, actions] using hwindow
  have hbounds := refinedLocalCorruptionWindow_scalar_bounds
    armCount horizonMass reciprocalGap corruption harmCount hhorizonMass
      hreciprocalGap hcountGap hwindow'
  exact
    integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit
      model armLaw hprob hbound hmean source hsuboptimal hgapPos horizon
        hbounds.2.2.2.2 hbounds.1 hbounds.2.1 hbounds.2.2.1
          hbounds.2.2.2.1

end Tsallis
end BanditRLProof
