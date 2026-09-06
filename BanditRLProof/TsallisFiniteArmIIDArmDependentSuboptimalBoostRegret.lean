import BanditRLProof.TsallisFiniteArmIIDHistoryAdaptiveRefinedCorruptedRewardLaw

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- A stationary but arm-dependent corruption process that leaves the best arm
unchanged and adds a prescribed nonnegative boost to every other arm. -/
noncomputable def armDependentSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (boost : Fin K -> Real)
    (hboost : forall arm, 0 <= boost arm) :
    FiniteArmIIDHistoryAdaptiveRewardShiftSource K where
  initial arm := if arm = model.bestArm then 0 else boost arm
  successor _ _ arm := if arm = model.bestArm then 0 else boost arm
  measurable_successor _ :=
    (measurable_of_countable
      (fun arm : Fin K => if arm = model.bestArm then 0 else boost arm)).comp
        measurable_snd
  envelope _ arm := if arm = model.bestArm then 0 else boost arm
  envelope_nonneg _ arm := by
    split_ifs
    · exact le_rfl
    · exact hboost arm
  initial_abs_le arm := by
    split_ifs <;> simp [abs_of_nonneg (hboost arm)]
  successor_abs_le _ _ arm := by
    split_ifs <;> simp [abs_of_nonneg (hboost arm)]

/-- The arm-dependent suboptimal boost has exact deterministic envelope budget
`(T+1) * sum_(a != best) boost(a)`. -/
theorem finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_armDependentSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Fin K -> Real) (hboost : forall arm, 0 <= boost arm) :
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon
        (armDependentSuboptimalRewardBoostSource model boost hboost) =
      (((horizon + 1 : Nat) : Real)) *
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum boost := by
  rw [finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_eq]
  simp only [armDependentSuboptimalRewardBoostSource]
  simp only [if_true, add_zero]
  have hinner :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => if arm = model.bestArm then 0 else boost arm) =
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum boost := by
    apply Finset.sum_congr rfl
    intro arm harm
    rw [if_neg (Finset.ne_of_mem_erase harm)]
  calc
    (Finset.range (horizon + 1)).sum (fun _ =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => if arm = model.bestArm then 0 else boost arm)) =
      (Finset.range (horizon + 1)).sum (fun _ =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum boost) := by
        apply Finset.sum_congr rfl
        intro _ _
        exact hinner
    _ = (((horizon + 1 : Nat) : Real)) *
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum boost := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]

/-- The coefficient-aware refined regime for an arm-dependent boost budget. -/
noncomputable def finiteArmIIDArmDependentSuboptimalBoostRefinedRegime
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Fin K -> Real) : Prop :=
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let totalBoost := actions.sum boost
  let corruption := horizonMass * totalBoost
  25 * reciprocalGap ^ 2 <= armCount * horizonMass ∧
    corruption * reciprocalGap <= armCount * horizonMass ∧
      25 * reciprocalGap *
          (Real.log
            ((2 * armCount * horizonMass) /
              (25 * reciprocalGap ^ 2)) + 2) <=
        corruption

/-- The named arm-dependent refined regime supplies the existing model-facing
compact corruption window after the exact budget rewrite. -/
theorem finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_armDependentSuboptimalRewardBoostSource_of_refinedRegime
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Fin K -> Real) (hboost : forall arm, 0 <= boost arm)
    (hregime : finiteArmIIDArmDependentSuboptimalBoostRefinedRegime
      model horizon boost) :
    finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow model horizon
      (armDependentSuboptimalRewardBoostSource model boost hboost) := by
  rw [finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow,
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_armDependentSuboptimalRewardBoostSource]
  exact hregime

/-- Total regret bound for arm-dependent boosts: the refined local expression
inside its named regime and the logarithmic additive-budget expression on the
complement. -/
noncomputable def finiteArmIIDArmDependentSuboptimalBoostAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (boost : Fin K -> Real) : Real := by
  classical
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let totalBoost := actions.sum boost
  let scale := 2 * armCount * horizonMass
  let corruption := horizonMass * totalBoost
  exact if finiteArmIIDArmDependentSuboptimalBoostRefinedRegime
      model horizon boost then
    1 + Real.log horizonMass +
      10 * Real.sqrt (corruption * reciprocalGap) *
        (2 + Real.sqrt
          (Real.log (scale / (corruption * reciprocalGap)) + 1))
  else
    (1 + Real.log horizonMass) * (1 + 25 * reciprocalGap) + corruption

/-- Scheduled half-Tsallis regret for every nonnegative arm-dependent
suboptimal reward boost and every finite horizon. The result automatically
selects the refined or logarithmic branch and requires no caller window proof. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDArmDependentSuboptimalBoostRewardLawRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (boost : Fin K -> Real) (hboost : forall arm, 0 <= boost arm)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let source := armDependentSuboptimalRewardBoostSource model boost hboost
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
      finiteArmIIDArmDependentSuboptimalBoostAllRegimeBound
        model horizon boost := by
  classical
  let source := armDependentSuboptimalRewardBoostSource model boost hboost
  by_cases hregime : finiteArmIIDArmDependentSuboptimalBoostRefinedRegime
      model horizon boost
  · have hwindow : finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow
        model horizon source := by
      simpa only [source] using
        finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_armDependentSuboptimalRewardBoostSource_of_refinedRegime
          model horizon boost hboost hregime
    have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
        model armLaw hprob hbound hmean source hsuboptimal hgapPos hgapLeOne
          horizon hwindow
    simpa only [source,
      finiteArmIIDArmDependentSuboptimalBoostAllRegimeBound, hregime, if_pos,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_armDependentSuboptimalRewardBoostSource]
      using hroute
  · have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_log
        model armLaw hprob hbound hmean source hgapPos horizon
    simpa only [source,
      finiteArmIIDArmDependentSuboptimalBoostAllRegimeBound, hregime, if_neg,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_armDependentSuboptimalRewardBoostSource]
      using hroute

end Tsallis
end BanditRLProof
