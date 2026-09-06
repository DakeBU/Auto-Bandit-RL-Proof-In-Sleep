import BanditRLProof.TsallisFiniteArmIIDMeasurableHistoryArmGatedSuboptimalBoostRegret
import BanditRLProof.TsallisScheduledReferenceGapExpectedDeviationSelfBounding

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- The reward shift selected from the finite observed pair history available
before round `t`. -/
noncomputable def finiteArmIIDHistoryAdaptiveRewardShiftAt
    {K : Nat} (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (t : Nat) (trajectory : (k : Nat) -> Fin K × Real) (arm : Fin K) : Real :=
  match t with
  | 0 => source.initial arm
  | n + 1 => source.successor n (Preorder.frestrictLe n trajectory) arm

/-- The realized predictable shift of a fixed arm is measurable on the full
trajectory space. -/
theorem measurable_finiteArmIIDHistoryAdaptiveRewardShiftAt
    {K : Nat} (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (t : Nat) (arm : Fin K) :
    Measurable (fun trajectory : (k : Nat) -> Fin K × Real =>
      finiteArmIIDHistoryAdaptiveRewardShiftAt source t trajectory arm) := by
  cases t with
  | zero => exact measurable_const
  | succ n =>
      change Measurable (fun trajectory : (k : Nat) -> Fin K × Real =>
        source.successor n (Preorder.frestrictLe n trajectory) arm)
      exact (source.measurable_successor n).comp
        ((Preorder.measurable_frestrictLe n).prodMk
          (measurable_const : Measurable
            (fun _ : ((k : Nat) -> Fin K × Real) => arm)))

/-- The realized shift retains the deterministic envelope supplied by the
history-adaptive source. -/
theorem abs_finiteArmIIDHistoryAdaptiveRewardShiftAt_le
    {K : Nat} (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (t : Nat) (trajectory : (k : Nat) -> Fin K × Real) (arm : Fin K) :
    |finiteArmIIDHistoryAdaptiveRewardShiftAt source t trajectory arm| <=
      source.envelope t arm := by
  cases t with
  | zero => exact source.initial_abs_le arm
  | succ n =>
      simpa only [finiteArmIIDHistoryAdaptiveRewardShiftAt] using
        source.successor_abs_le n (Preorder.frestrictLe n trajectory) arm

/-- The actual/reference predictable loss-gap deviation is controlled by the
two shifts realized on the observed history, before replacing them by their
deterministic envelopes. -/
theorem abs_historyAdaptiveCorruptedPredictableLossDiff_sub_baseLossDiff_le_actualShift
    {K : Nat} (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (t : Nat) (sample : (Nat -> (Fin K -> Rat)) ×
      ((k : Nat) -> Fin K × Real)) (best arm : Fin K) :
    |(Exp3.predictableLossAt
          (finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source)
            t sample arm -
        Exp3.predictableLossAt
          (finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source)
            t sample best) -
      (Exp3.predictableLossAt
          (iidLossStatePredictableLossVector finiteArmIIDRewardVectorLoss
            measurable_finiteArmIIDRewardVectorLoss
            finiteArmIIDRewardVectorLoss_nonneg
            finiteArmIIDRewardVectorLoss_le_one)
            t sample arm -
        Exp3.predictableLossAt
          (iidLossStatePredictableLossVector finiteArmIIDRewardVectorLoss
            measurable_finiteArmIIDRewardVectorLoss
            finiteArmIIDRewardVectorLoss_nonneg
            finiteArmIIDRewardVectorLoss_le_one)
            t sample best)| <=
      |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 arm| +
        |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 best| := by
  cases t with
  | zero =>
      simpa only [
        predictableLossAt_finiteArmIIDHistoryAdaptiveCorruptedRewardLoss_zero,
        predictableLossAt_iidLossStatePredictableLossVector,
        finiteArmIIDHistoryAdaptiveRewardShiftAt] using
        abs_stationaryCorruptedLossDiff_sub_baseLossDiff_le
          source.initial (sample.1 0) best arm
  | succ n =>
      simpa only [
        predictableLossAt_finiteArmIIDHistoryAdaptiveCorruptedRewardLoss_succ,
        predictableLossAt_iidLossStatePredictableLossVector,
        finiteArmIIDHistoryAdaptiveRewardShiftAt] using
        abs_stationaryCorruptedLossDiff_sub_baseLossDiff_le
          (source.successor n (Preorder.frestrictLe n sample.2))
          (sample.1 (n + 1)) best arm

/-- Probability-weighted realized history-adaptive deviation is integrable
under every finite trajectory measure. -/
theorem integrable_sampledScheduledHalfTsallisProbability_mul_historyAdaptiveRewardShiftDeviation
    {Env : Type*} {K : Nat} [MeasurableSpace Env]
    (mu : Measure (Env × ((k : Nat) -> Fin K × Real))) [IsFiniteMeasure mu]
    (arms : Finset (Fin K)) (harms : arms.Nonempty) (eta : Nat -> Real)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (t : Nat) (best arm : Fin K) (harm : arm ∈ arms) :
    Integrable (fun sample =>
      sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample arm *
        (|finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 arm| +
          |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 best|))
      mu := by
  have hprob := measurable_sampledScheduledHalfTsallisProbabilityAtTime
    (Env := Env) arms harms eta t arm harm
  have hshift (candidate : Fin K) : Measurable (fun sample :
      Env × ((k : Nat) -> Fin K × Real) =>
      finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 candidate) :=
    (measurable_finiteArmIIDHistoryAdaptiveRewardShiftAt
      source t candidate).comp measurable_snd
  have hmeas : Measurable (fun sample :
      Env × ((k : Nat) -> Fin K × Real) =>
      sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample arm *
        (|finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 arm| +
          |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 best|)) :=
    hprob.mul ((hshift arm).abs.add (hshift best).abs)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (source.envelope t arm + source.envelope t best) ?_
  exact Filter.Eventually.of_forall fun sample => by
    have hp := finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample
    have hp0 := hp.1 arm harm
    have hp1 := finiteSimplex_apply_le_one hp harm
    have hdevNonneg : 0 <=
        |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 arm| +
          |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 best| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have henvelopeNonneg : 0 <=
        source.envelope t arm + source.envelope t best :=
      add_nonneg (source.envelope_nonneg t arm)
        (source.envelope_nonneg t best)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 hdevNonneg)]
    calc
      sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample arm *
          (|finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 arm| +
            |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 best|) <=
          sampledScheduledHalfTsallisProbabilityAtTime
              arms harms eta t sample arm *
            (source.envelope t arm + source.envelope t best) :=
        mul_le_mul_of_nonneg_left
          (add_le_add
            (abs_finiteArmIIDHistoryAdaptiveRewardShiftAt_le
              source t sample.2 arm)
            (abs_finiteArmIIDHistoryAdaptiveRewardShiftAt_le
              source t sample.2 best)) hp0
      _ <= 1 * (source.envelope t arm + source.envelope t best) :=
        mul_le_mul_of_nonneg_right hp1 henvelopeNonneg
      _ = source.envelope t arm + source.envelope t best := one_mul _

/-- Expected corruption weighted by the generated policy's conditional
selection probability for each affected suboptimal arm, using the realized
history-adaptive shifts. -/
noncomputable def finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (mu : Measure ((Nat -> Fin K -> Rat) ×
      ((k : Nat) -> Fin K × Real))) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum (fun arm =>
      integral mu (fun sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
            (Finset.univ : Finset (Fin K))
            ⟨model.bestArm, Finset.mem_univ model.bestArm⟩
            sampledScheduledHalfTsallisSqrtSchedule t sample arm *
          (|finiteArmIIDHistoryAdaptiveRewardShiftAt
              source t sample.2 arm| +
            |finiteArmIIDHistoryAdaptiveRewardShiftAt
              source t sample.2 model.bestArm|))))

theorem finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget_eq
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (mu : Measure ((Nat -> Fin K -> Rat) ×
      ((k : Nat) -> Fin K × Real))) :
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
        model horizon source mu =
      (Finset.range (horizon + 1)).sum (fun t =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum (fun arm =>
          integral mu (fun sample =>
            sampledScheduledHalfTsallisProbabilityAtTime
                (Finset.univ : Finset (Fin K))
                ⟨model.bestArm, Finset.mem_univ model.bestArm⟩
                sampledScheduledHalfTsallisSqrtSchedule t sample arm *
              (|finiteArmIIDHistoryAdaptiveRewardShiftAt
                  source t sample.2 arm| +
                |finiteArmIIDHistoryAdaptiveRewardShiftAt
                  source t sample.2 model.bestArm|)))) := by
  rfl

/-- The policy-weighted realized corruption budget is nonnegative. -/
theorem finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget_nonneg
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (mu : Measure ((Nat -> Fin K -> Rat) ×
      ((k : Nat) -> Fin K × Real))) :
    0 <= finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
      model horizon source mu := by
  rw [finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget_eq]
  apply Finset.sum_nonneg
  intro t _ht
  apply Finset.sum_nonneg
  intro arm harm
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun sample =>
    mul_nonneg
      ((finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
          (Finset.univ : Finset (Fin K))
          ⟨model.bestArm, Finset.mem_univ model.bestArm⟩
          sampledScheduledHalfTsallisSqrtSchedule t sample).1 arm
        (Finset.mem_of_mem_erase harm))
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- The expected realized budget never exceeds the source's deterministic
all-round envelope budget. -/
theorem finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget_le
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (mu : Measure ((Nat -> Fin K -> Rat) ×
      ((k : Nat) -> Fin K × Real))) [IsProbabilityMeasure mu] :
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
        model horizon source mu <=
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget
        model horizon source := by
  rw [finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget_eq,
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_eq]
  apply Finset.sum_le_sum
  intro t _ht
  apply Finset.sum_le_sum
  intro arm harm
  let harms : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨model.bestArm, Finset.mem_univ model.bestArm⟩
  have hintegrable :=
    integrable_sampledScheduledHalfTsallisProbability_mul_historyAdaptiveRewardShiftDeviation
      mu (Finset.univ : Finset (Fin K)) harms
        sampledScheduledHalfTsallisSqrtSchedule source t model.bestArm arm
        (Finset.mem_of_mem_erase harm)
  have hmono := integral_mono_ae hintegrable (integrable_const _) <|
    Filter.Eventually.of_forall fun sample => by
      have hp := finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
        (Finset.univ : Finset (Fin K)) harms
          sampledScheduledHalfTsallisSqrtSchedule t sample
      have hp0 := hp.1 arm (Finset.mem_of_mem_erase harm)
      have hp1 := finiteSimplex_apply_le_one hp
        (Finset.mem_of_mem_erase harm)
      have henvelopeNonneg : 0 <=
          source.envelope t arm + source.envelope t model.bestArm :=
        add_nonneg (source.envelope_nonneg t arm)
          (source.envelope_nonneg t model.bestArm)
      calc
        sampledScheduledHalfTsallisProbabilityAtTime
              (Finset.univ : Finset (Fin K)) harms
              sampledScheduledHalfTsallisSqrtSchedule t sample arm *
            (|finiteArmIIDHistoryAdaptiveRewardShiftAt
                source t sample.2 arm| +
              |finiteArmIIDHistoryAdaptiveRewardShiftAt
                source t sample.2 model.bestArm|) <=
            sampledScheduledHalfTsallisProbabilityAtTime
                (Finset.univ : Finset (Fin K)) harms
                sampledScheduledHalfTsallisSqrtSchedule t sample arm *
              (source.envelope t arm +
                source.envelope t model.bestArm) :=
          mul_le_mul_of_nonneg_left
            (add_le_add
              (abs_finiteArmIIDHistoryAdaptiveRewardShiftAt_le
                source t sample.2 arm)
              (abs_finiteArmIIDHistoryAdaptiveRewardShiftAt_le
                source t sample.2 model.bestArm)) hp0
        _ <= 1 * (source.envelope t arm +
              source.envelope t model.bestArm) :=
          mul_le_mul_of_nonneg_right hp1 henvelopeNonneg
        _ = source.envelope t arm + source.envelope t model.bestArm :=
          one_mul _
  have hconst : integral mu (fun _sample :
      (Nat -> Fin K -> Rat) × ((k : Nat) -> Fin K × Real) =>
        source.envelope t arm + source.envelope t model.bestArm) =
      source.envelope t arm + source.envelope t model.bestArm := by
    simp
  rw [hconst] at hmono
  simpa only [harms] using hmono

/-- The finite-arm IID history-adaptive model satisfies self-bounding with the
exact policy-weighted realized corruption budget. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLaw_hasSelfBounding
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
      finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
        model horizon source mu <=
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
  let deviation := fun (t : Nat)
      (sample : (Nat -> Fin K -> Rat) × ((k : Nat) -> Fin K × Real))
      (arm : Fin K) =>
    |finiteArmIIDHistoryAdaptiveRewardShiftAt source t sample.2 arm| +
      |finiteArmIIDHistoryAdaptiveRewardShiftAt
        source t sample.2 model.bestArm|
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
  have hdeviationIntegrable : forall t, t <= horizon -> forall arm,
      arm ∈ arms.erase model.bestArm ->
      Integrable (fun sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample arm * deviation t sample arm) mu := by
    intro t _ht arm harm
    simpa only [deviation] using
      integrable_sampledScheduledHalfTsallisProbability_mul_historyAdaptiveRewardShiftDeviation
        mu arms harms eta source t model.bestArm arm
          (Finset.mem_of_mem_erase harm)
  have hdeviation : forall t, t <= horizon -> forall sample arm,
      arm ∈ arms.erase model.bestArm ->
      |(Exp3.predictableLossAt loss t sample arm -
            Exp3.predictableLossAt loss t sample model.bestArm) -
          (Exp3.predictableLossAt referenceLoss t sample arm -
            Exp3.predictableLossAt referenceLoss t sample model.bestArm)| <=
        deviation t sample arm := by
    intro t _ht sample arm _harm
    simpa only [loss, referenceLoss, deviation] using
      abs_historyAdaptiveCorruptedPredictableLossDiff_sub_baseLossDiff_le_actualShift
        source t sample model.bestArm arm
  have hselfBounding :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_referenceExpectedGapLaw_of_expectedDeviation
      mu arms harms eta loss referenceLoss (Finset.mem_univ model.bestArm)
      baseGap deviation horizon hreferenceGapLaw hdeviationIntegrable
        hdeviation
  simpa only [arms, harms, eta, selector, prior, trajectoryKernel, mu, loss,
    baseGap, deviation,
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget] using
      hselfBounding

/-- The square-root schedule gives logarithmic regret with the exact expected
realized history-adaptive corruption budget. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_log
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
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
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
        finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
          model horizon source mu := by
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
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
      model horizon source mu
  have hselfBounding :=
    integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLaw_hasSelfBounding
      model armLaw hprob hbound hmean source horizon
  have hharmonic :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_of_selfBounding
      prior arms harms loss (Finset.mem_univ model.bestArm) horizon baseGap
      (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
      corruption
      (by simpa only [law, loss, arms, harms, selector, prior, mu, baseGap,
        corruption] using hselfBounding)
  let gapFactor := 1 + 25 * (arms.erase model.bestArm).sum
    (fun arm => 1 / baseGap arm)
  have hgapSum : 0 <= (arms.erase model.bestArm).sum
      (fun arm => 1 / baseGap arm) := by
    apply Finset.sum_nonneg
    intro arm harm
    exact le_of_lt (one_div_pos.mpr
      (hgapPos arm (Finset.ne_of_mem_erase harm)))
  have hgapFactor : 0 <= gapFactor := by
    dsimp only [gapFactor]
    nlinarith
  have hbudget := sampledScheduledHalfTsallisHarmonicBudget_le_one_add_log
    horizon
  have hmul : sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor :=
    mul_le_mul_of_nonneg_right hbudget hgapFactor
  dsimp only at hharmonic
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass model.bestArm) horizon) <=
      sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor +
        corruption := by
      simpa only [gapFactor, baseGap] using hharmonic
    _ <= (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor +
        corruption := by
      linarith
    _ = (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
        finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
          model horizon source mu := by
      rfl

/-- The generated-law specialization of the expected realized corruption
budget, packaged without exposing the trajectory measure to callers. -/
noncomputable def finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (horizon : Nat) : Real := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  let law := finiteArmIIDRewardVectorLaw armLaw
  let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule loss
  let prior := Measure.infinitePi (fun _ : Nat => law)
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  exact finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget
    model horizon source mu

/-- The coefficient-aware refined window evaluated at the generated policy's
expected realized history-adaptive corruption. -/
noncomputable def finiteArmIIDHistoryAdaptiveExpectedRefinedCorruptionWindow
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (horizon : Nat) : Prop :=
  RefinedLocalCorruptionWindow
    (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real)
    (((horizon + 1 : Nat) : Real))
    (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
      (fun arm => 1 / ((model.gap arm : Rat) : Real)))
    (finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw
      model armLaw source horizon)

/-- Refined local regret using the policy-weighted realized corruption budget.
The compact window discharges the low-level scalar tuning inequalities. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
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
    (hwindow : finiteArmIIDHistoryAdaptiveExpectedRefinedCorruptionWindow
      model armLaw source horizon) :
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
      finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw
        model armLaw source horizon
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
  let actions := arms.erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum (fun arm => 1 / baseGap arm)
  let corruption :=
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw
      model armLaw source horizon
  have harmCount : 1 <= armCount := by
    dsimp [armCount, actions, arms]
    exact_mod_cast hsuboptimal.card_pos
  have hhorizonMass : 0 < horizonMass := by
    dsimp [horizonMass]
    positivity
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap, actions, arms, baseGap]
    exact sum_inv_pos_of_nonempty
      ((Finset.univ : Finset (Fin K)).erase model.bestArm)
        hsuboptimal (fun arm => ((model.gap arm : Rat) : Real))
        (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
  have hcountGap : armCount <= reciprocalGap := by
    calc
      armCount = actions.sum (fun _ => (1 : Real)) := by
        simp [armCount]
      _ <= actions.sum (fun arm => 1 / baseGap arm) := by
        apply Finset.sum_le_sum
        intro arm harm
        have hpos := hgapPos arm (Finset.ne_of_mem_erase harm)
        rw [le_div_iff₀ hpos]
        simpa only [baseGap, one_mul] using
          hgapLeOne arm (Finset.ne_of_mem_erase harm)
      _ = reciprocalGap := by rfl
  have hwindow' : RefinedLocalCorruptionWindow
      armCount horizonMass reciprocalGap corruption := by
    simpa only [finiteArmIIDHistoryAdaptiveExpectedRefinedCorruptionWindow,
      armCount, horizonMass, reciprocalGap, corruption, actions, arms,
      baseGap] using hwindow
  have hbounds := refinedLocalCorruptionWindow_scalar_bounds
    armCount horizonMass reciprocalGap corruption harmCount hhorizonMass
      hreciprocalGap hcountGap hwindow'
  have hselfBounding :=
    integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLaw_hasSelfBounding
      model armLaw hprob hbound hmean source horizon
  have hselfBounding' :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase model.bestArm).sum (fun arm =>
            baseGap arm * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms sampledScheduledHalfTsallisSqrtSchedule t arm)) -
        corruption <=
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass model.bestArm) horizon) := by
    simpa only [law, loss, arms, harms, selector, prior, mu, baseGap,
      corruption,
      finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw] using
        hselfBounding
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedLocalExplicit
      prior arms harms loss (Finset.mem_univ model.bestArm) horizon baseGap
        (by simpa only [actions] using hsuboptimal)
        (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
        corruption hbounds.2.2.2.2 hbounds.1 hbounds.2.1
          hbounds.2.2.1 hbounds.2.2.2.1 hselfBounding'
  simpa only [law, loss, arms, harms, selector, prior, mu, baseGap,
    reciprocalGap, horizonMass, corruption, actions, armCount] using hroute

/-- Total regret envelope using the refined expected-corruption expression
when there is a suboptimal arm and the compact window holds, and the
logarithmic expected-corruption expression otherwise. -/
noncomputable def finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (horizon : Nat) : Real := by
  classical
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let scale := 2 * armCount * horizonMass
  let corruption :=
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw
      model armLaw source horizon
  exact if actions.Nonempty ∧
      finiteArmIIDHistoryAdaptiveExpectedRefinedCorruptionWindow
        model armLaw source horizon then
    1 + Real.log horizonMass +
      10 * Real.sqrt (corruption * reciprocalGap) *
        (2 + Real.sqrt
          (Real.log (scale / (corruption * reciprocalGap)) + 1))
  else
    (1 + Real.log horizonMass) * (1 + 25 * reciprocalGap) + corruption

/-- With one arm there is no suboptimal coordinate and the expected
corruption all-regimes envelope reduces to the logarithmic base term. -/
@[simp]
theorem finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound_fin_one
    (model : FiniteBanditModel 1) (armLaw : Fin 1 -> Measure Rat)
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource 1)
    (horizon : Nat) :
    finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound
        model armLaw source horizon =
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  have hbest : model.bestArm = 0 := Subsingleton.elim _ _
  simp [finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound,
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw,
    finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudget, hbest]

/-- Scheduled half-Tsallis regret for every finite-arm IID history-adaptive
reward-shift source and finite horizon, using the policy-weighted realized
corruption budget in both automatically selected regimes. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (source : FiniteArmIIDHistoryAdaptiveRewardShiftSource K)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
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
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound
        model armLaw source horizon := by
  classical
  by_cases hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty
  · by_cases hwindow :
        finiteArmIIDHistoryAdaptiveExpectedRefinedCorruptionWindow
          model armLaw source horizon
    · have hroute :=
        integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
          model armLaw hprob hbound hmean source hsuboptimal hgapPos hgapLeOne
            horizon hwindow
      simpa only [finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound,
        hsuboptimal, hwindow, and_self, if_pos] using hroute
    · have hroute :=
        integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_log
          model armLaw hprob hbound hmean source hgapPos horizon
      simpa only [finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound,
        hsuboptimal, hwindow, and_false, if_neg,
        finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw] using
          hroute
  · have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_log
        model armLaw hprob hbound hmean source hgapPos horizon
    simpa only [finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound,
      hsuboptimal, false_and, if_neg,
      finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw] using
        hroute

/-- Measurable history-arm-gated suboptimal boosts inherit the all-regimes
bound with gate-open corruption weighted by conditional selection probability,
rather than the full deterministic boost schedule. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDMeasurableHistoryArmGatedSuboptimalBoostExpectedCorruptionRewardLawRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (initialGate : Set (Fin K))
    (gate : (n : Nat) ->
      Set (History.FinitePairHistory (Fin K) Real n × Fin K))
    (hgate : forall n, MeasurableSet (gate n))
    (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let source := measurableHistoryArmGatedSuboptimalRewardBoostSource
      model initialGate gate hgate boost hboost
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
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound model armLaw
        source horizon := by
  let source := measurableHistoryArmGatedSuboptimalRewardBoostSource
    model initialGate gate hgate boost hboost
  simpa only [source] using
    integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_allRegimes
      model armLaw hprob hbound hmean source hgapPos hgapLeOne horizon

end Tsallis
end BanditRLProof
