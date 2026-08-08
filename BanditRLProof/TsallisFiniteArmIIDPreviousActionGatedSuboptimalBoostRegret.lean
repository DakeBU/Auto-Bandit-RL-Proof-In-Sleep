import BanditRLProof.TsallisFiniteArmIIDTimeVaryingSuboptimalBoostRegret

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- A concrete history-adaptive corruption source. At successor time `n+1`,
the suboptimal-arm boost is active exactly when the action observed at time `n`
equals `triggerArm`. The best arm is never shifted. -/
noncomputable def previousActionGatedSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (triggerArm : Fin K)
    (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm) :
    FiniteArmIIDHistoryAdaptiveRewardShiftSource K where
  initial arm := if arm = model.bestArm then 0 else boost 0 arm
  successor n history arm :=
    if arm = model.bestArm then 0
    else if (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 = triggerArm then
      boost (n + 1) arm
    else 0
  measurable_successor n := by
    let previousIndex : Finset.Iic n := ⟨n, Finset.mem_Iic.mpr le_rfl⟩
    have hpreviousPair : Measurable
        (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
          input.1 previousIndex) :=
      (measurable_pi_apply previousIndex).comp measurable_fst
    have hpreviousAction : Measurable
        (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
          (input.1 previousIndex).1) :=
      measurable_fst.comp hpreviousPair
    have hbest : MeasurableSet
        {input : History.FinitePairHistory (Fin K) Real n × Fin K |
          input.2 = model.bestArm} :=
      measurableSet_eq_fun measurable_snd measurable_const
    have htrigger : MeasurableSet
        {input : History.FinitePairHistory (Fin K) Real n × Fin K |
          (input.1 previousIndex).1 = triggerArm} :=
      measurableSet_eq_fun hpreviousAction measurable_const
    have hscheduled : Measurable
        (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
          boost (n + 1) input.2) :=
      (measurable_of_countable (boost (n + 1))).comp measurable_snd
    exact Measurable.ite hbest measurable_const
      (Measurable.ite htrigger hscheduled measurable_const)
  envelope t arm := if arm = model.bestArm then 0 else boost t arm
  envelope_nonneg t arm := by
    split_ifs
    · exact le_rfl
    · exact hboost t arm
  initial_abs_le arm := by
    split_ifs <;> simp [abs_of_nonneg (hboost 0 arm)]
  successor_abs_le n _ arm := by
    split_ifs
    · simp
    · simp [abs_of_nonneg (hboost (n + 1) arm)]
    · simpa using hboost (n + 1) arm

/-- The deterministic envelope of the previous-action-gated source has the
same exact double finite-sum budget as its ungated time-varying schedule. -/
theorem finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_previousActionGatedSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (triggerArm : Fin K)
    (horizon : Nat) (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm) :
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon
        (previousActionGatedSuboptimalRewardBoostSource
          model triggerArm boost hboost) =
      finiteArmIIDTimeVaryingSuboptimalBoostBudget model horizon boost := by
  rw [finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_eq]
  simp only [previousActionGatedSuboptimalRewardBoostSource, if_true, add_zero,
    finiteArmIIDTimeVaryingSuboptimalBoostBudget]
  apply Finset.sum_congr rfl
  intro t _ht
  apply Finset.sum_congr rfl
  intro arm harm
  rw [if_neg (Finset.ne_of_mem_erase harm)]

/-- The time-varying named regime supplies the compact refined window for the
history-adaptive previous-action-gated source. -/
theorem finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_previousActionGatedSuboptimalRewardBoostSource_of_refinedRegime
    {K : Nat} (model : FiniteBanditModel K) (triggerArm : Fin K)
    (horizon : Nat) (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm)
    (hregime : finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
      model horizon boost) :
    finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow model horizon
      (previousActionGatedSuboptimalRewardBoostSource
        model triggerArm boost hboost) := by
  rw [finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow,
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_previousActionGatedSuboptimalRewardBoostSource]
  exact hregime

/-- Scheduled half-Tsallis regret for a concrete source whose successor boost
depends on the previous sampled action. The theorem covers every finite horizon
and internally selects the refined or logarithmic branch. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDPreviousActionGatedSuboptimalBoostRewardLawRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (triggerArm : Fin K) (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let source := previousActionGatedSuboptimalRewardBoostSource
      model triggerArm boost hboost
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
  let source := previousActionGatedSuboptimalRewardBoostSource
    model triggerArm boost hboost
  by_cases hregime : finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
      model horizon boost
  · have hwindow : finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow
        model horizon source := by
      simpa only [source] using
        finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_previousActionGatedSuboptimalRewardBoostSource_of_refinedRegime
          model triggerArm horizon boost hboost hregime
    have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
        model armLaw hprob hbound hmean source hsuboptimal hgapPos hgapLeOne
          horizon hwindow
    simpa only [source,
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound, hregime, if_pos,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_previousActionGatedSuboptimalRewardBoostSource]
      using hroute
  · have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_log
        model armLaw hprob hbound hmean source hgapPos horizon
    simpa only [source,
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound, hregime, if_neg,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_previousActionGatedSuboptimalRewardBoostSource]
      using hroute

end Tsallis
end BanditRLProof
