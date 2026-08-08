import BanditRLProof.TsallisFiniteArmIIDTimeVaryingSuboptimalBoostRegret

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- A history-adaptive corruption source with an arbitrary initial arm gate and
arbitrary measurable finite-pair-history-and-arm successor gates. The best arm
is never shifted. -/
noncomputable def measurableHistoryArmGatedSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K)
    (initialGate : Set (Fin K))
    (gate : (n : Nat) ->
      Set (History.FinitePairHistory (Fin K) Real n × Fin K))
    (hgate : forall n, MeasurableSet (gate n))
    (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm) :
    FiniteArmIIDHistoryAdaptiveRewardShiftSource K where
  initial arm := by
    classical
    exact if arm = model.bestArm then 0
      else if arm ∈ initialGate then boost 0 arm else 0
  successor n history arm := by
    classical
    exact if arm = model.bestArm then 0
      else if (history, arm) ∈ gate n then boost (n + 1) arm else 0
  measurable_successor n := by
    classical
    have hbest : MeasurableSet
        {input : History.FinitePairHistory (Fin K) Real n × Fin K |
          input.2 = model.bestArm} :=
      measurableSet_eq_fun measurable_snd measurable_const
    have hscheduled : Measurable
        (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
          boost (n + 1) input.2) :=
      (measurable_of_countable (boost (n + 1))).comp measurable_snd
    exact Measurable.ite hbest measurable_const
      (Measurable.ite (hgate n) hscheduled measurable_const)
  envelope t arm := if arm = model.bestArm then 0 else boost t arm
  envelope_nonneg t arm := by
    split_ifs
    · exact le_rfl
    · exact hboost t arm
  initial_abs_le arm := by
    classical
    split_ifs
    · simp
    · simp [abs_of_nonneg (hboost 0 arm)]
    · simpa using hboost 0 arm
  successor_abs_le n _ arm := by
    classical
    split_ifs
    · simp
    · simp [abs_of_nonneg (hboost (n + 1) arm)]
    · simpa using hboost (n + 1) arm

/-- The measurable history-arm gate does not enlarge the deterministic
envelope, whose budget is exactly the underlying time-varying schedule. -/
theorem finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_measurableHistoryArmGatedSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K)
    (initialGate : Set (Fin K))
    (gate : (n : Nat) ->
      Set (History.FinitePairHistory (Fin K) Real n × Fin K))
    (hgate : forall n, MeasurableSet (gate n))
    (horizon : Nat) (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm) :
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon
        (measurableHistoryArmGatedSuboptimalRewardBoostSource
          model initialGate gate hgate boost hboost) =
      finiteArmIIDTimeVaryingSuboptimalBoostBudget model horizon boost := by
  rw [finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_eq]
  simp only [measurableHistoryArmGatedSuboptimalRewardBoostSource, if_true,
    add_zero, finiteArmIIDTimeVaryingSuboptimalBoostBudget]
  apply Finset.sum_congr rfl
  intro t _ht
  apply Finset.sum_congr rfl
  intro arm harm
  rw [if_neg (Finset.ne_of_mem_erase harm)]

/-- The named time-varying refined regime supplies the compact window for an
arbitrary measurable history-arm-gated source with the same envelope. -/
theorem finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_measurableHistoryArmGatedSuboptimalRewardBoostSource_of_refinedRegime
    {K : Nat} (model : FiniteBanditModel K)
    (initialGate : Set (Fin K))
    (gate : (n : Nat) ->
      Set (History.FinitePairHistory (Fin K) Real n × Fin K))
    (hgate : forall n, MeasurableSet (gate n))
    (horizon : Nat) (boost : Nat -> Fin K -> Real)
    (hboost : forall t arm, 0 <= boost t arm)
    (hregime : finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
      model horizon boost) :
    finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow model horizon
      (measurableHistoryArmGatedSuboptimalRewardBoostSource
        model initialGate gate hgate boost hboost) := by
  rw [finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow,
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_measurableHistoryArmGatedSuboptimalRewardBoostSource]
  exact hregime

/-- Scheduled half-Tsallis regret for every initial arm gate and measurable
predictable successor gate on the complete finite pair history and candidate
arm. The theorem covers every finite horizon and selects the refined or
logarithmic branch internally. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDMeasurableHistoryArmGatedSuboptimalBoostRewardLawRegret_le_allRegimes
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
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
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
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound
        model horizon boost := by
  classical
  let source := measurableHistoryArmGatedSuboptimalRewardBoostSource
    model initialGate gate hgate boost hboost
  by_cases hregime : finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime
      model horizon boost
  · have hwindow : finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow
        model horizon source := by
      simpa only [source] using
        finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_measurableHistoryArmGatedSuboptimalRewardBoostSource_of_refinedRegime
          model initialGate gate hgate horizon boost hboost hregime
    have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
        model armLaw hprob hbound hmean source hsuboptimal hgapPos hgapLeOne
          horizon hwindow
    simpa only [source,
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound, hregime, if_pos,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_measurableHistoryArmGatedSuboptimalRewardBoostSource]
      using hroute
  · have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_log
        model armLaw hprob hbound hmean source hgapPos horizon
    simpa only [source,
      finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound, hregime, if_neg,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_measurableHistoryArmGatedSuboptimalRewardBoostSource]
      using hroute

end Tsallis
end BanditRLProof
