import BanditRLProof.TsallisScheduledInitialExpectedStability

/-!
# Expected scheduled half-Tsallis stability at all actual times

This module joins the distinct time-zero and successor conditioning surfaces.
Its final left side is exactly the full `Finset.range (horizon + 1)` stability
sum consumed by the scheduled pathwise regret decomposition.

All included local rates must lie in `(0, 1 / 2]`.  The coarse fallback for
larger early rates remains a separate leaf.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- One actual scheduled successor potential term is integrable under the
canonical generated trajectory. -/
theorem integrable_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (n + 1)) (heta_le : eta (n + 1) <= 1 / 2) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample (n + 1)) mu := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hhistory : Measurable
      (sampledScheduledHalfTsallisHistoryAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable
      (sampledScheduledHalfTsallisActionAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.comp
      ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hcond :
      condDistrib
          (sampledScheduledHalfTsallisActionAt
            (Env := Env) (Action := Action) n)
          (sampledScheduledHalfTsallisHistoryAt n) mu =ᵐ[
        mu.map (sampledScheduledHalfTsallisHistoryAt n)]
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n := by
    simpa [mu, sampledScheduledHalfTsallisHistoryAt,
      sampledScheduledHalfTsallisActionAt,
      sampledScheduledHalfTsallisPolicyAt] using
      (sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta selector.finiteHistory loss.environment n)
  have hproduct : Integrable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n) ⊗ₘ
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n) := by
    simpa [mu, selector] using
      (integrable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        prior arms harms eta loss n heta heta_le)
  have hscoreComp : Integrable (fun sample =>
      sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n
        (sampledScheduledHalfTsallisHistoryAt n sample,
          sampledScheduledHalfTsallisActionAt n sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu (sampledScheduledHalfTsallisHistoryAt n) hhistory
      (sampledScheduledHalfTsallisActionAt n) haction
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (sampledScheduledHalfTsallisPolicyAt (Env := Env)
        arms harms eta selector.finiteHistory n)
      hcond hproduct
  have hterm :=
    sampledScheduledHalfTsallisPotentialStabilityAtTime_succ_eq_historyAction_ae
      prior arms harms eta loss n
  dsimp only at hterm
  exact hscoreComp.congr hterm.symm

/-- The complete scheduled successor stability sum is integrable. -/
theorem integrable_sum_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real)
    (heta : forall n, n < horizon -> 0 < eta (n + 1))
    (heta_le : forall n, n < horizon -> eta (n + 1) <= 1 / 2)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample => (Finset.range horizon).sum (fun n =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample (n + 1))) mu := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  exact IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
    (fun n sample => sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta sample (n + 1))
    (fun n hn => by
      simpa [mu, selector] using
        (integrable_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime
          prior arms harms eta loss n
          (heta n (Finset.mem_range.mp hn))
          (heta_le n (Finset.mem_range.mp hn))))

/-- The full scheduled stability sum from time zero through `horizon` is
integrable under the canonical generated trajectory. -/
theorem integrable_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real)
    (heta : forall t, t <= horizon -> 0 < eta t)
    (heta_le : forall t, t <= horizon -> eta t <= 1 / 2)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample t)) mu := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hinitial :=
    integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_refined
      prior arms harms eta (heta 0 (Nat.zero_le horizon))
        (heta_le 0 (Nat.zero_le horizon)) loss
  dsimp only at hinitial
  have hsuccessor :=
    integrable_sum_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime
      prior horizon arms harms eta
      (fun n hn => heta (n + 1) (Nat.succ_le_iff.mpr hn))
      (fun n hn => heta_le (n + 1) (Nat.succ_le_iff.mpr hn)) loss
  dsimp only at hsuccessor
  have hadd := hinitial.1.add hsuccessor
  simpa [Finset.sum_range_succ', add_comm] using hadd

/-!
Expected refined stability for every actual time from zero through `horizon`.
The left side is exactly the stability sum in
`sampledScheduledHalfTsallisEstimatedRegret_eq_stability_add_penalty`.
-/
theorem integral_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_refined
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real)
    (heta : forall t, t <= horizon -> 0 < eta t)
    (heta_le : forall t, t <= horizon -> eta t <= 1 / 2)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t)) <=
      integral mu (fun sample =>
        sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
            (Env := Env) arms harms eta sample.1 +
          (Finset.range horizon).sum (fun n =>
            sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
              (Env := Env) arms harms eta n
              (sampledScheduledHalfTsallisHistoryAt n sample))) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let initialTerm := fun sample : Env × ((k : Nat) -> Action × Real) =>
    sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta sample 0
  let successorSum := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun n =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample (n + 1))
  let initialBound := fun sample : Env × ((k : Nat) -> Action × Real) =>
    sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
      (Env := Env) arms harms eta sample.1
  let successorBoundSum := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    (Finset.range horizon).sum (fun n =>
      sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n
        (sampledScheduledHalfTsallisHistoryAt n sample))
  have hzero : 0 <= horizon := Nat.zero_le horizon
  have hinitial :=
    integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_refined
      prior arms harms eta (heta 0 hzero) (heta_le 0 hzero) loss
  dsimp only at hinitial
  have hsuccessor :=
    integral_sum_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_refined
      prior horizon arms harms eta
      (fun n hn => heta (n + 1) (Nat.succ_le_iff.mpr hn))
      (fun n hn => heta_le (n + 1) (Nat.succ_le_iff.mpr hn)) loss
  dsimp only at hsuccessor
  have hsuccessorIntegrable : Integrable successorSum mu := by
    simpa [successorSum, mu, selector] using
      (integrable_sum_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime
        prior horizon arms harms eta
        (fun n hn => heta (n + 1) (Nat.succ_le_iff.mpr hn))
        (fun n hn => heta_le (n + 1) (Nat.succ_le_iff.mpr hn)) loss)
  have hhistory (n : Nat) : Measurable
      (sampledScheduledHalfTsallisHistoryAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have hinitialBoundMap : Integrable
      (sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
        (Env := Env) arms harms eta) (mu.map Prod.fst) :=
    integrable_sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
      (mu.map Prod.fst) arms harms eta (heta 0 hzero)
  have hinitialBoundIntegrable : Integrable initialBound mu := by
    simpa [initialBound, Function.comp_def] using
      hinitialBoundMap.comp_measurable measurable_fst
  have hsuccessorBound (n : Nat) (hn : n < horizon) : Integrable
      (sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n)) :=
    integrable_sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
      n (mu.map (sampledScheduledHalfTsallisHistoryAt n))
      arms harms eta (heta (n + 1) (Nat.succ_le_iff.mpr hn))
      selector.finiteHistory
  have hsuccessorBoundComp (n : Nat) (hn : n < horizon) : Integrable
      (fun sample =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample)) mu := by
    simpa [Function.comp_def] using
      (hsuccessorBound n hn).comp_measurable (hhistory n)
  have hsuccessorBoundIntegrable : Integrable successorBoundSum mu := by
    unfold successorBoundSum
    exact IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun n sample =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample))
      (fun n hn => hsuccessorBoundComp n (Finset.mem_range.mp hn))
  have hleftAdd := integral_add hinitial.1 hsuccessorIntegrable
  have hrightAdd := integral_add hinitialBoundIntegrable
    hsuccessorBoundIntegrable
  have hleft :
      integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample t)) =
        integral mu initialTerm + integral mu successorSum := by
    calc
      integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample t)) =
        integral mu (fun sample => initialTerm sample + successorSum sample) := by
          congr 1
          funext sample
          simp [initialTerm, successorSum, Finset.sum_range_succ', add_comm]
      _ = integral mu initialTerm + integral mu successorSum := by
        simpa only [Pi.add_apply] using hleftAdd
  have hright :
      integral mu (fun sample => initialBound sample + successorBoundSum sample) =
        integral mu initialBound + integral mu successorBoundSum := by
    simpa only [Pi.add_apply] using hrightAdd
  calc
    integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t)) =
      integral mu initialTerm + integral mu successorSum := hleft
    _ <= integral mu initialBound + integral mu successorBoundSum :=
      add_le_add
        (by simpa [initialTerm, initialBound, mu, selector] using hinitial.2)
        (by simpa [successorSum, successorBoundSum, mu, selector] using hsuccessor)
    _ = integral mu (fun sample => initialBound sample +
        successorBoundSum sample) := hright.symm
    _ = integral mu (fun sample =>
        sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
            (Env := Env) arms harms eta sample.1 +
          (Finset.range horizon).sum (fun n =>
            sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
              (Env := Env) arms harms eta n
              (sampledScheduledHalfTsallisHistoryAt n sample))) := by
      rfl

end Tsallis
end BanditRLProof
