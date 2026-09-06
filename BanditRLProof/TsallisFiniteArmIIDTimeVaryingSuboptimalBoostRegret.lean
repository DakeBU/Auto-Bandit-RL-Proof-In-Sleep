import BanditRLProof.TsallisFiniteArmIIDHistoryAdaptiveRefinedCorruptedRewardLaw

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- A deterministic time-and-arm-dependent corruption process that leaves the
best arm unchanged and adds a prescribed nonnegative boost to every other arm. -/
noncomputable def timeVaryingSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm) :
    FiniteArmIIDHistoryAdaptiveRewardShiftSource K where
  initial arm := if arm = model.bestArm then 0 else boost 0 arm
  successor n _ arm :=
    if arm = model.bestArm then 0 else boost (n + 1) arm
  measurable_successor n :=
    (measurable_of_countable
      (fun arm : Fin K =>
        if arm = model.bestArm then 0 else boost (n + 1) arm)).comp
      measurable_snd
  envelope t arm := if arm = model.bestArm then 0 else boost t arm
  envelope_nonneg t arm := by
    split_ifs
    · exact le_rfl
    · exact hboost t arm
  initial_abs_le arm := by
    split_ifs <;> simp [abs_of_nonneg (hboost 0 arm)]
  successor_abs_le n _ arm := by
    split_ifs <;> simp [abs_of_nonneg (hboost (n + 1) arm)]

/-- Exact deterministic corruption mass of a time-varying suboptimal-arm
boost through the inclusive horizon. -/
noncomputable def finiteArmIIDTimeVaryingSuboptimalBoostBudget
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Nat -> Fin K -> Real) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum (boost t))

/-- The source envelope budget is exactly the finite time-and-arm boost sum. -/
theorem finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_timeVaryingSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Nat -> Fin K -> Real) (hboost : forall t arm, 0 <= boost t arm) :
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon
        (timeVaryingSuboptimalRewardBoostSource model boost hboost) =
      finiteArmIIDTimeVaryingSuboptimalBoostBudget model horizon boost := by
  rw [finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_eq]
  simp only [timeVaryingSuboptimalRewardBoostSource, if_true, add_zero,
    finiteArmIIDTimeVaryingSuboptimalBoostBudget]
  apply Finset.sum_congr rfl
  intro t _ht
  apply Finset.sum_congr rfl
  intro arm harm
  rw [if_neg (Finset.ne_of_mem_erase harm)]

/-- The coefficient-aware refined regime for a time-varying suboptimal-arm
boost budget. -/
noncomputable def finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Nat -> Fin K -> Real) : Prop :=
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let corruption :=
    finiteArmIIDTimeVaryingSuboptimalBoostBudget model horizon boost
  25 * reciprocalGap ^ 2 <= armCount * horizonMass ∧
    corruption * reciprocalGap <= armCount * horizonMass ∧
      25 * reciprocalGap *
          (Real.log
            ((2 * armCount * horizonMass) /
              (25 * reciprocalGap ^ 2)) + 2) <=
        corruption

/-- The named time-varying refined regime supplies the existing model-facing
compact corruption window after the exact budget rewrite. -/
theorem finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_timeVaryingSuboptimalRewardBoostSource_of_refinedRegime
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Nat -> Fin K -> Real) (hboost : forall t arm, 0 <= boost t arm)
    (hregime : finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
      model horizon boost) :
    finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow model horizon
      (timeVaryingSuboptimalRewardBoostSource model boost hboost) := by
  rw [finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow,
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_timeVaryingSuboptimalRewardBoostSource]
  exact hregime

/-- Total regret bound for deterministic time-varying boosts: the refined
local expression inside its named regime and the logarithmic additive-budget
expression on the complement. -/
noncomputable def finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Nat -> Fin K -> Real) : Real := by
  classical
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let scale := 2 * armCount * horizonMass
  let corruption :=
    finiteArmIIDTimeVaryingSuboptimalBoostBudget model horizon boost
  exact if finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
      model horizon boost then
    1 + Real.log horizonMass +
      10 * Real.sqrt (corruption * reciprocalGap) *
        (2 + Real.sqrt
          (Real.log (scale / (corruption * reciprocalGap)) + 1))
  else
    (1 + Real.log horizonMass) * (1 + 25 * reciprocalGap) + corruption

/-- Scheduled half-Tsallis regret for every deterministic nonnegative
time-varying suboptimal reward boost and every finite horizon. The theorem
selects the refined or logarithmic branch and requires no caller window proof. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDTimeVaryingSuboptimalBoostRewardLawRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let source := timeVaryingSuboptimalRewardBoostSource model boost hboost
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
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound
        model horizon boost := by
  classical
  let source := timeVaryingSuboptimalRewardBoostSource model boost hboost
  by_cases hregime : finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
      model horizon boost
  · have hwindow : finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow
        model horizon source := by
      simpa only [source] using
        finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_timeVaryingSuboptimalRewardBoostSource_of_refinedRegime
          model horizon boost hboost hregime
    have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
        model armLaw hprob hbound hmean source hsuboptimal hgapPos hgapLeOne
          horizon hwindow
    simpa only [source,
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound, hregime, if_pos,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_timeVaryingSuboptimalRewardBoostSource]
      using hroute
  · have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_log
        model armLaw hprob hbound hmean source hgapPos horizon
    simpa only [source,
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound, hregime, if_neg,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_timeVaryingSuboptimalRewardBoostSource]
      using hroute

end Tsallis
end BanditRLProof
