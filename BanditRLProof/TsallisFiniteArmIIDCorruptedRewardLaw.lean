import BanditRLProof.TsallisFiniteArmIIDRewardLaw
import BanditRLProof.TsallisSqrtScheduleFixedGap
import Mathlib.Topology.UnitInterval

/-!
# Stationary corrupted finite-arm IID reward laws for scheduled half-Tsallis

This module replaces the free nonnegative `corruption` parameter of the
abstract self-bounding endpoint by a quantity derived from a concrete process.
Each arm receives a fixed real reward shift, the shifted reward is projected
back to `[0, 1]`, and fresh finite reward vectors remain IID across rounds.

The route is deliberately stationary and oblivious.  History-dependent or
time-varying corruptions require a later predictable-law transport.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

/-- Projection of a real value to the unit interval. -/
noncomputable def clippedUnitReal (value : Real) : Real :=
  (Set.projIcc (0 : Real) 1 zero_le_one value : Real)

theorem clippedUnitReal_mem_Icc (value : Real) :
    clippedUnitReal value ∈ Set.Icc (0 : Real) 1 := by
  exact (Set.projIcc (0 : Real) 1 zero_le_one value).property

theorem clippedUnitReal_eq_of_mem_Icc (value : Real)
    (hvalue : value ∈ Set.Icc (0 : Real) 1) :
    clippedUnitReal value = value := by
  simpa [clippedUnitReal] using
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hvalue)

theorem abs_clippedUnitReal_add_sub_self_le (value shift : Real)
    (hvalue : value ∈ Set.Icc (0 : Real) 1) :
    |clippedUnitReal (value + shift) - value| <= |shift| := by
  have hcontraction := Set.abs_projIcc_sub_projIcc
    (a := (0 : Real)) (b := 1) zero_le_one
    (c := value + shift) (d := value)
  calc
    |clippedUnitReal (value + shift) - value| =
        |clippedUnitReal (value + shift) - clippedUnitReal value| := by
      rw [clippedUnitReal_eq_of_mem_Icc value hvalue]
    _ <= |(value + shift) - value| := by
      simpa only [clippedUnitReal] using hcontraction
    _ = |shift| := by ring_nf

/-- Reward after a stationary arm-dependent shift and unit-interval clipping. -/
noncomputable def finiteArmIIDStationaryCorruptedReward {K : Nat}
    (rewardShift : Fin K -> Real) (state : Fin K -> Rat) (arm : Fin K) : Real :=
  clippedUnitReal (clippedUnitReward (state arm) + rewardShift arm)

/-- Selected loss associated with the stationary corrupted reward vector. -/
noncomputable def finiteArmIIDStationaryCorruptedRewardVectorLoss {K : Nat}
    (rewardShift : Fin K -> Real) (state : Fin K -> Rat) (arm : Fin K) : Real :=
  1 - finiteArmIIDStationaryCorruptedReward rewardShift state arm

theorem measurable_finiteArmIIDStationaryCorruptedRewardVectorLoss {K : Nat}
    (rewardShift : Fin K -> Real) :
    Measurable (fun input : (Fin K -> Rat) × Fin K =>
      finiteArmIIDStationaryCorruptedRewardVectorLoss
        rewardShift input.1 input.2) := by
  exact measurable_of_countable _

theorem finiteArmIIDStationaryCorruptedRewardVectorLoss_nonneg {K : Nat}
    (rewardShift : Fin K -> Real) (state : Fin K -> Rat) (arm : Fin K) :
    0 <= finiteArmIIDStationaryCorruptedRewardVectorLoss
      rewardShift state arm := by
  have hmem := clippedUnitReal_mem_Icc
    (clippedUnitReward (state arm) + rewardShift arm)
  dsimp only [finiteArmIIDStationaryCorruptedRewardVectorLoss,
    finiteArmIIDStationaryCorruptedReward]
  linarith [hmem.2]

theorem finiteArmIIDStationaryCorruptedRewardVectorLoss_le_one {K : Nat}
    (rewardShift : Fin K -> Real) (state : Fin K -> Rat) (arm : Fin K) :
    finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift state arm <= 1 := by
  have hmem := clippedUnitReal_mem_Icc
    (clippedUnitReward (state arm) + rewardShift arm)
  dsimp only [finiteArmIIDStationaryCorruptedRewardVectorLoss,
    finiteArmIIDStationaryCorruptedReward]
  linarith [hmem.1]

theorem abs_finiteArmIIDStationaryCorruptedReward_sub_base_le {K : Nat}
    (rewardShift : Fin K -> Real) (state : Fin K -> Rat) (arm : Fin K) :
    |finiteArmIIDStationaryCorruptedReward rewardShift state arm -
        clippedUnitReward (state arm)| <= |rewardShift arm| := by
  exact abs_clippedUnitReal_add_sub_self_le _ _
    ⟨clippedUnitReward_nonneg (state arm),
      clippedUnitReward_le_one (state arm)⟩

theorem abs_stationaryCorruptedLossDiff_sub_baseLossDiff_le {K : Nat}
    (rewardShift : Fin K -> Real) (state : Fin K -> Rat)
    (best arm : Fin K) :
    |(finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift state arm -
          finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift state best) -
        (finiteArmIIDRewardVectorLoss state arm -
          finiteArmIIDRewardVectorLoss state best)| <=
      |rewardShift arm| + |rewardShift best| := by
  have harm := abs_finiteArmIIDStationaryCorruptedReward_sub_base_le
    rewardShift state arm
  have hbest := abs_finiteArmIIDStationaryCorruptedReward_sub_base_le
    rewardShift state best
  calc
    |(finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift state arm -
          finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift state best) -
        (finiteArmIIDRewardVectorLoss state arm -
          finiteArmIIDRewardVectorLoss state best)| =
        |(finiteArmIIDStationaryCorruptedReward rewardShift state best -
            clippedUnitReward (state best)) -
          (finiteArmIIDStationaryCorruptedReward rewardShift state arm -
            clippedUnitReward (state arm))| := by
      congr 1
      simp only [finiteArmIIDStationaryCorruptedRewardVectorLoss,
        finiteArmIIDRewardVectorLoss]
      ring
    _ <= |finiteArmIIDStationaryCorruptedReward rewardShift state best -
            clippedUnitReward (state best)| +
          |finiteArmIIDStationaryCorruptedReward rewardShift state arm -
            clippedUnitReward (state arm)| := abs_sub _ _
    _ <= |rewardShift best| + |rewardShift arm| := add_le_add hbest harm
    _ = |rewardShift arm| + |rewardShift best| := add_comm _ _

theorem integrable_iidLossStateDiff
    {LossState Action : Type*} [MeasurableSpace LossState]
    [MeasurableSpace Action]
    (law : Measure LossState) [IsFiniteMeasure law]
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : forall state action, 0 <= value state action)
    (hvalue_le_one : forall state action, value state action <= 1)
    (best arm : Action) :
    Integrable (fun state => value state arm - value state best) law := by
  have hmeas : Measurable (fun state => value state arm - value state best) :=
    (hvalue.comp (measurable_id.prodMk measurable_const)).sub
      (hvalue.comp (measurable_id.prodMk measurable_const))
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun state => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hvalue_nonneg state arm,
      hvalue_le_one state arm, hvalue_nonneg state best,
      hvalue_le_one state best]

/-- The actual stationary-corrupted IID loss gap remains within the two
affected arm shifts of the uncorrupted finite-bandit model gap. -/
theorem abs_iidLossStateMeanGap_stationaryCorrupted_sub_modelGap_le
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (rewardShift : Fin K -> Real) (arm : Fin K) :
    |iidLossStateMeanGap (finiteArmIIDRewardVectorLaw armLaw)
          (finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift)
          model.bestArm arm - ((model.gap arm : Rat) : Real)| <=
      |rewardShift arm| + |rewardShift model.bestArm| := by
  letI (i : Fin K) : IsProbabilityMeasure (armLaw i) := hprob i
  let law := finiteArmIIDRewardVectorLaw armLaw
  letI : IsProbabilityMeasure law := by
    dsimp only [law, finiteArmIIDRewardVectorLaw]
    infer_instance
  let actual := finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift
  let base := finiteArmIIDRewardVectorLoss (K := K)
  have hactualIntegrable : Integrable
      (fun state => actual state arm - actual state model.bestArm) law := by
    exact integrable_iidLossStateDiff law actual
      (measurable_finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift)
      (finiteArmIIDStationaryCorruptedRewardVectorLoss_nonneg rewardShift)
      (finiteArmIIDStationaryCorruptedRewardVectorLoss_le_one rewardShift)
      model.bestArm arm
  have hbaseIntegrable : Integrable
      (fun state => base state arm - base state model.bestArm) law := by
    exact integrable_iidLossStateDiff law base
      measurable_finiteArmIIDRewardVectorLoss
      finiteArmIIDRewardVectorLoss_nonneg finiteArmIIDRewardVectorLoss_le_one
      model.bestArm arm
  have hbaseGap : iidLossStateMeanGap law base model.bestArm arm =
      ((model.gap arm : Rat) : Real) := by
    exact iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap
      model armLaw hprob hbound hmean arm
  have heq :
      iidLossStateMeanGap law actual model.bestArm arm -
          ((model.gap arm : Rat) : Real) =
        integral law (fun state =>
          (actual state arm - actual state model.bestArm) -
            (base state arm - base state model.bestArm)) := by
    rw [← hbaseGap]
    exact (integral_sub hactualIntegrable hbaseIntegrable).symm
  rw [heq, ← Real.norm_eq_abs]
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := law) (C := |rewardShift arm| + |rewardShift model.bestArm|)
    (Filter.Eventually.of_forall fun state => by
      rw [Real.norm_eq_abs]
      exact abs_stationaryCorruptedLossDiff_sub_baseLossDiff_le
        rewardShift state model.bestArm arm)
  simpa [law] using hnorm

/-- Total baseline-gap perturbation allowance through the inclusive horizon. -/
noncomputable def scheduledGapDeviationBudget
    {Action : Type*} [DecidableEq Action]
    (arms : Finset Action) (best : Action) (horizon : Nat)
    (deviation : Action -> Real) : Real :=
  (Finset.range (horizon + 1)).sum (fun _ =>
    (arms.erase best).sum deviation)

theorem scheduledGapDeviationBudget_eq
    {Action : Type*} [DecidableEq Action]
    (arms : Finset Action) (best : Action) (horizon : Nat)
    (deviation : Action -> Real) :
    scheduledGapDeviationBudget arms best horizon deviation =
      (((horizon + 1 : Nat) : Real)) * (arms.erase best).sum deviation := by
  simp [scheduledGapDeviationBudget, nsmul_eq_mul]

/-- An expected law for perturbed gaps yields the baseline-gap self-bound with
the accumulated coordinatewise gap-deviation budget. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_perturbedExpectedGapLaw
    {Env Action : Type*}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (baseGap actualGap deviation : Action -> Real)
    (hactualGapLaw : HasScheduledExpectedGapLaw
      mu arms harms eta loss best actualGap horizon)
    (hdeviation : forall action, action ∈ arms.erase best ->
      |actualGap action - baseGap action| <= deviation action) :
    (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) -
      scheduledGapDeviationBudget arms best horizon deviation <=
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss (pointMass best) horizon) := by
  have hregret :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalExpectedGapMass_of_expectedGapLaw
      mu arms harms eta loss hbest actualGap horizon hactualGapLaw
  have hbaseLe :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) <=
        (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            actualGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action + deviation action)) := by
    apply Finset.sum_le_sum
    intro t _ht
    apply Finset.sum_le_sum
    intro action haction
    let probability := sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action
    have hsimplex :=
      finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t
    have hp0 : 0 <= probability :=
      hsimplex.1 action (Finset.mem_of_mem_erase haction)
    have hp1 : probability <= 1 :=
      finiteSimplex_apply_le_one hsimplex
        (Finset.mem_of_mem_erase haction)
    have habs : baseGap action - actualGap action <=
        |actualGap action - baseGap action| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have hweighted :
        (baseGap action - actualGap action) * probability <=
          deviation action := by
      calc
        (baseGap action - actualGap action) * probability <=
            |actualGap action - baseGap action| * probability :=
          mul_le_mul_of_nonneg_right habs hp0
        _ <= |actualGap action - baseGap action| := by
          simpa using mul_le_of_le_one_right (abs_nonneg _) hp1
        _ <= deviation action := hdeviation action haction
    dsimp only [probability] at hweighted ⊢
    linarith
  have hsplit :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            actualGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action + deviation action)) =
        (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            actualGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) +
          scheduledGapDeviationBudget arms best horizon deviation := by
    simp only [Finset.sum_add_distrib, scheduledGapDeviationBudget]
  rw [hsplit] at hbaseLe
  rw [hregret]
  linarith

/-- Explicit corruption budget for a stationary arm-dependent reward shift. -/
noncomputable def finiteArmIIDStationaryRewardCorruptionBudget {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat)
    (rewardShift : Fin K -> Real) : Real :=
  scheduledGapDeviationBudget (Finset.univ : Finset (Fin K)) model.bestArm
    horizon (fun arm => |rewardShift arm| + |rewardShift model.bestArm|)

theorem finiteArmIIDStationaryRewardCorruptionBudget_eq {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat)
    (rewardShift : Fin K -> Real) :
    finiteArmIIDStationaryRewardCorruptionBudget model horizon rewardShift =
      (((horizon + 1 : Nat) : Real)) *
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => |rewardShift arm| + |rewardShift model.bestArm|) := by
  exact scheduledGapDeviationBudget_eq _ _ _ _

@[simp]
theorem finiteArmIIDStationaryRewardCorruptionBudget_zero {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat) :
    finiteArmIIDStationaryRewardCorruptionBudget model horizon
      (fun _ => 0) = 0 := by
  simp [finiteArmIIDStationaryRewardCorruptionBudget,
    scheduledGapDeviationBudget]

/-- Scheduled half-Tsallis logarithmic regret for an IID finite-arm reward
model with a fixed clipped reward shift.  The additive corruption term is
derived from `rewardShift`; it is not a free theorem parameter. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDStationaryCorruptedRewardLawRegret_le_log
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (rewardShift : Fin K -> Real)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIIDRewardVectorLaw armLaw
    let value := finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift
    let loss := iidLossStatePredictableLossVector value
      (measurable_finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift)
      (finiteArmIIDStationaryCorruptedRewardVectorLoss_nonneg rewardShift)
      (finiteArmIIDStationaryCorruptedRewardVectorLoss_le_one rewardShift)
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
        finiteArmIIDStationaryRewardCorruptionBudget
          model horizon rewardShift := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (arm : Fin K) : IsProbabilityMeasure (armLaw arm) := hprob arm
  let law := finiteArmIIDRewardVectorLaw armLaw
  letI : IsProbabilityMeasure law := by
    dsimp only [law, finiteArmIIDRewardVectorLaw]
    infer_instance
  let value := finiteArmIIDStationaryCorruptedRewardVectorLoss rewardShift
  let hvalue := measurable_finiteArmIIDStationaryCorruptedRewardVectorLoss
    rewardShift
  let hvalueNonneg :=
    finiteArmIIDStationaryCorruptedRewardVectorLoss_nonneg rewardShift
  let hvalueLeOne :=
    finiteArmIIDStationaryCorruptedRewardVectorLoss_le_one rewardShift
  let loss := iidLossStatePredictableLossVector value hvalue
    hvalueNonneg hvalueLeOne
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms eta loss
  let prior := Measure.infinitePi (fun _ : Nat => law)
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let mu := prior ⊗ₘ trajectoryKernel
  let actualGap := iidLossStateMeanGap law value model.bestArm
  let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
  let deviation := fun arm : Fin K =>
    |rewardShift arm| + |rewardShift model.bestArm|
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, eta, loss, value, hvalue,
      hvalueNonneg, hvalueLeOne] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTrajectoryKernel
        (fun _ : Fin K => (0 : Rat)) value hvalue hvalueNonneg hvalueLeOne
        arms harms eta selector.finiteHistory horizon
  have hindependent : HasScheduledIndependentMeanGapLaw
      mu arms loss model.bestArm actualGap horizon := by
    simpa only [mu, prior, trajectoryKernel, actualGap, loss] using
      hasScheduledIndependentMeanGapLaw_of_iidLossState
        law value hvalue hvalueNonneg hvalueLeOne arms model.bestArm horizon
          trajectoryKernel hfactor
  have hactualGapLaw : HasScheduledExpectedGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon := by
    exact hasScheduledExpectedGapLaw_of_independentMeanGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon hindependent
  have hdeviation : forall arm, arm ∈ arms.erase model.bestArm ->
      |actualGap arm - baseGap arm| <= deviation arm := by
    intro arm _harm
    exact abs_iidLossStateMeanGap_stationaryCorrupted_sub_modelGap_le
      model armLaw hprob hbound hmean rewardShift arm
  have hselfBounding :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase model.bestArm).sum (fun arm =>
            baseGap arm * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t arm)) -
        scheduledGapDeviationBudget arms model.bestArm horizon deviation <=
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass model.bestArm) horizon) := by
    exact
      integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_perturbedExpectedGapLaw
        mu arms harms eta loss (Finset.mem_univ model.bestArm) horizon
        baseGap actualGap deviation hactualGapLaw hdeviation
  have hharmonic :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_of_selfBounding
      prior arms harms loss (Finset.mem_univ model.bestArm) horizon baseGap
      (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
      (scheduledGapDeviationBudget arms model.bestArm horizon deviation)
      (by simpa only [mu, trajectoryKernel, selector, eta] using hselfBounding)
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
        arms harms eta loss (pointMass model.bestArm) horizon) <=
      sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor +
        scheduledGapDeviationBudget arms model.bestArm horizon deviation := by
      simpa only [gapFactor, eta, baseGap] using hharmonic
    _ <= (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor +
        scheduledGapDeviationBudget arms model.bestArm horizon deviation := by
      linarith
    _ = (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
        finiteArmIIDStationaryRewardCorruptionBudget
          model horizon rewardShift := by
      rfl

end Tsallis
end BanditRLProof
