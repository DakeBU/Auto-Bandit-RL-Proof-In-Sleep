import BanditRLProof.TsallisScheduledIIDMeanGap

/-!
# History-adaptive predictable losses on IID states

The loss chosen at a successor round may inspect the complete pre-action pair
history.  It may inspect the fresh IID state only through the current state
coordinate.  This coordinate-locality contract is exactly what is needed for
the canonical visible trajectory to factor through every finite state prefix.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- A predictable loss family reads state coordinate `0` initially and state
coordinate `n + 1` after a history of length `n + 1`.  The successor value may
otherwise depend arbitrarily and measurably on that pre-action history. -/
structure HasIIDStateCoordinateLocality
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [MeasurableSpace Action]
    (loss : Exp3.PredictableLossVector (Nat -> LossState) Action) : Prop where
  initial_congr : forall environment1 environment2 action,
    environment1 0 = environment2 0 ->
      loss.initial environment1 action = loss.initial environment2 action
  successor_congr : forall n environment1 environment2 history action,
    environment1 (n + 1) = environment2 (n + 1) ->
      loss.successor n environment1 history action =
        loss.successor n environment2 history action

/-- Equal IID state prefixes generate equal visible trajectory prefixes for a
history-adaptive coordinate-local predictable loss family. -/
theorem sampledScheduledHalfTsallisTrajectoryKernel_map_frestrictLe_eq_of_iidStateCoordinateLocality_prefix_eq
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [StandardBorelSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (loss : Exp3.PredictableLossVector (Nat -> LossState) Action)
    (hlocal : HasIIDStateCoordinateLocality loss)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta)
    (environment1 environment2 : Nat -> LossState) (n : Nat)
    (henvironment : Preorder.frestrictLe n environment1 =
      Preorder.frestrictLe n environment2) :
    (sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector loss.environment environment1).map
        (Preorder.frestrictLe n) =
      (sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector loss.environment environment2).map
        (Preorder.frestrictLe n) := by
  let algorithm := sampledScheduledHalfTsallisHistoryAlgorithm
    arms harms eta selector
  have hcoordinate : forall t, t <= n -> environment1 t = environment2 t := by
    intro t ht
    have h := congrFun henvironment
      (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n)
    simpa [Preorder.frestrictLe_apply] using h
  have hinitialFeedback :
      (loss.environment.at environment1).initialFeedback =
        (loss.environment.at environment2).initialFeedback := by
    ext action event hevent
    have hvalue := hlocal.initial_congr environment1 environment2 action
      (hcoordinate 0 (Nat.zero_le n))
    simp [Thompson.MeasurableHistoryEnvironment.at,
      Exp3.PredictableLossVector.environment, Kernel.comap_apply,
      Kernel.deterministic_apply, hvalue]
  have hfeedback : forall k, k < n ->
      (loss.environment.at environment1).feedback k =
        (loss.environment.at environment2).feedback k := by
    intro k hk
    ext input event hevent
    have hvalue := hlocal.successor_congr k environment1 environment2
      input.1 input.2 (hcoordinate (k + 1) (Nat.succ_le_of_lt hk))
    simp [Thompson.MeasurableHistoryEnvironment.at,
      Exp3.PredictableLossVector.environment, Kernel.comap_apply,
      Kernel.deterministic_apply, hvalue]
  rw [sampledScheduledHalfTsallisTrajectoryKernel,
    Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical,
    Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical]
  apply KernelTrajectoryPrefix.trajMeasure_map_frestrictLe_congr
  · rw [hinitialFeedback]
  · intro k hk
    unfold Thompson.historyStepKernel
    rw [hfeedback k hk]

/-- Finite visible-prefix kernel induced by a coordinate-local predictable
loss family on an IID state trace. -/
noncomputable def sampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernel
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Nonempty Action] [DecidableEq Action]
    (fallback : LossState)
    (loss : Exp3.PredictableLossVector (Nat -> LossState) Action)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    Kernel ((i : Finset.Iic n) -> LossState)
      (History.FinitePairHistory Action Real n) :=
  ((sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector loss.environment).comap
      (extendLossStatePrefix fallback n)
      (measurable_extendLossStatePrefix fallback n)).map
    (Preorder.frestrictLe n)

instance instSampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernelIsMarkov
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Nonempty Action] [DecidableEq Action]
    (fallback : LossState)
    (loss : Exp3.PredictableLossVector (Nat -> LossState) Action)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    IsMarkovKernel
      (sampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernel fallback loss
        arms harms eta selector n) := by
  unfold sampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernel
  letI : IsMarkovKernel
      ((sampledScheduledHalfTsallisTrajectoryKernel
          arms harms eta selector loss.environment).comap
        (extendLossStatePrefix fallback n)
        (measurable_extendLossStatePrefix fallback n)) := by infer_instance
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (Preorder.measurable_frestrictLe n)

/-- The canonical scheduled trajectory of a history-adaptive coordinate-local
loss family factors through every finite IID state prefix. -/
theorem hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisHistoryAdaptiveTrajectoryKernel
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [StandardBorelSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (fallback : LossState)
    (loss : Exp3.PredictableLossVector (Nat -> LossState) Action)
    (hlocal : HasIIDStateCoordinateLocality loss)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (horizon : Nat) :
    HasScheduledIIDPrefixKernelFactorization
      (sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector loss.environment)
      horizon := by
  intro n _hn
  let prefixKernel := sampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernel
    fallback loss arms harms eta selector n
  refine ⟨prefixKernel, ?_, ?_⟩
  · exact instSampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernelIsMarkov
      fallback loss arms harms eta selector n
  · ext environment event hevent
    rw [Kernel.map_apply' _ (Preorder.measurable_frestrictLe n)
        environment hevent,
      Kernel.comap_apply,
      show prefixKernel =
          sampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernel
            fallback loss arms harms eta selector n from rfl,
      sampledScheduledHalfTsallisIIDHistoryAdaptivePrefixKernel,
      Kernel.map_apply' _ (Preorder.measurable_frestrictLe n)
        (Preorder.frestrictLe n environment) hevent,
      Kernel.comap_apply]
    have hprefix : Preorder.frestrictLe n environment =
        Preorder.frestrictLe n
          (extendLossStatePrefix fallback n
            (Preorder.frestrictLe n environment)) := by
      funext i
      simp [Preorder.frestrictLe_apply,
        extendLossStatePrefix_apply_of_le fallback n i.1
          (Finset.mem_Iic.mp i.2)]
    have hmap := congrArg (fun measure => measure event)
      (sampledScheduledHalfTsallisTrajectoryKernel_map_frestrictLe_eq_of_iidStateCoordinateLocality_prefix_eq
        loss hlocal arms harms eta selector environment
          (extendLossStatePrefix fallback n
            (Preorder.frestrictLe n environment)) n hprefix)
    dsimp only at hmap
    rw [Measure.map_apply (μ :=
          sampledScheduledHalfTsallisTrajectoryKernel
            arms harms eta selector loss.environment environment)
          (Preorder.measurable_frestrictLe n) hevent,
      Measure.map_apply (μ :=
          sampledScheduledHalfTsallisTrajectoryKernel
            arms harms eta selector loss.environment
            (extendLossStatePrefix fallback n
              (Preorder.frestrictLe n environment)))
          (Preorder.measurable_frestrictLe n) hevent] at hmap
    exact hmap

end Tsallis
end BanditRLProof
