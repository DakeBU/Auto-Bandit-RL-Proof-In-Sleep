import BanditRLProof.TsallisFTRLGeneratedMeasurability

/-!
# Scheduled recursive half-Tsallis trajectories

This module lifts the recursive pure half-Tsallis trajectory from a fixed
learning rate to a deterministic schedule.  The initial action uses `eta 0`;
after the visible prefix through round `n`, the successor policy uses
`eta (n + 1)`.  This indexing matches the scheduled FTRL penalty route.

The module constructs only the selector, score, policy, trajectory, and
conditional action law.  It does not prove a refined stability or regret
bound.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Roundwise selector regularity for a deterministic learning-rate schedule. -/
structure HalfTsallisScheduleFiniteHistorySelectorMeasurability
    {Action : Type u} [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) : Prop where
  round : forall t,
    HalfTsallisFiniteHistorySelectorMeasurability arms harms (eta t)

/-- The canonical selected minimizer satisfies the scheduled regularity
contract at every round. -/
noncomputable def canonicalHalfTsallisScheduleFiniteHistorySelectorMeasurability
    {Action : Type u} [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real) :
    HalfTsallisScheduleFiniteHistorySelectorMeasurability arms harms eta where
  round t := canonicalHalfTsallisFiniteHistorySelectorMeasurability
    arms harms (eta t)

/-- Cumulative importance-weighted score through an inclusive history under
the scheduled policies. -/
noncomputable def sampledScheduledHalfTsallisHistoryScore
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real) :
    (n : Nat) -> History.FinitePairHistory Action Real n -> Action -> Real
  | 0, history, action =>
      Exp3.importanceWeightedLoss
        (initialHalfTsallisDistribution arms harms (eta 0))
        (fun _ => (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2)
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 action
  | n + 1, history, action =>
      let previous := Exp3.previousPairHistory history
      sampledScheduledHalfTsallisHistoryScore arms harms eta n previous action +
        Exp3.importanceWeightedLoss
          (halfTsallisMinimizer arms harms (eta (n + 1))
            (sampledScheduledHalfTsallisHistoryScore
              arms harms eta n previous))
          (fun _ => (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 action

@[simp]
theorem sampledScheduledHalfTsallisHistoryScore_zero
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (history : History.FinitePairHistory Action Real 0) (action : Action) :
    sampledScheduledHalfTsallisHistoryScore arms harms eta 0 history action =
      Exp3.importanceWeightedLoss
        (initialHalfTsallisDistribution arms harms (eta 0))
        (fun _ => (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2)
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 action :=
  rfl

@[simp]
theorem sampledScheduledHalfTsallisHistoryScore_succ
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (n : Nat) (history : History.FinitePairHistory Action Real (n + 1))
    (action : Action) :
    sampledScheduledHalfTsallisHistoryScore arms harms eta (n + 1)
        history action =
      sampledScheduledHalfTsallisHistoryScore arms harms eta n
          (Exp3.previousPairHistory history) action +
        Exp3.importanceWeightedLoss
          (halfTsallisMinimizer arms harms (eta (n + 1))
            (sampledScheduledHalfTsallisHistoryScore arms harms eta n
              (Exp3.previousPairHistory history)))
          (fun _ => (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 action :=
  rfl

/-- Scheduled selector regularity makes every supported score coordinate
measurable. -/
theorem measurable_sampledScheduledHalfTsallisHistoryScore
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) :
    forall n action, action ∈ arms ->
      Measurable (fun history : History.FinitePairHistory Action Real n =>
        sampledScheduledHalfTsallisHistoryScore
          arms harms eta n history action) := by
  intro n
  induction n with
  | zero =>
      intro action _haction
      let zeroIndex : Finset.Iic 0 := ⟨0, Finset.mem_Iic.mpr le_rfl⟩
      have hchosen : Measurable
          (fun history : History.FinitePairHistory Action Real 0 =>
            (history zeroIndex).1) :=
        measurable_fst.comp (measurable_pi_apply zeroIndex)
      have hloss : Measurable
          (fun history : History.FinitePairHistory Action Real 0 =>
            (history zeroIndex).2) :=
        measurable_snd.comp (measurable_pi_apply zeroIndex)
      simpa [sampledScheduledHalfTsallisHistoryScore, zeroIndex] using
        (Exp3.measurable_observedImportanceWeightedLoss
          (fun _history : History.FinitePairHistory Action Real 0 =>
            initialHalfTsallisDistribution arms harms (eta 0))
          (fun history => (history zeroIndex).1)
          (fun history => (history zeroIndex).2)
          action measurable_const hchosen hloss)
  | succ n ih =>
      intro action haction
      let lastIndex : Finset.Iic (n + 1) :=
        ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
      have hprevious : Measurable
          (Exp3.previousPairHistory (Action := Action) (n := n)) :=
        Exp3.measurable_previousPairHistory
      have hscore : Measurable
          (fun history : History.FinitePairHistory Action Real (n + 1) =>
            sampledScheduledHalfTsallisHistoryScore arms harms eta n
              (Exp3.previousPairHistory history) action) :=
        (ih action haction).comp hprevious
      have hprob : Measurable
          (fun history : History.FinitePairHistory Action Real (n + 1) =>
            halfTsallisMinimizer arms harms (eta (n + 1))
              (sampledScheduledHalfTsallisHistoryScore arms harms eta n
                (Exp3.previousPairHistory history)) action) :=
        ((selector.round (n + 1)).measurable_selector n
          (sampledScheduledHalfTsallisHistoryScore arms harms eta n)
          (fun selected hselected => ih selected hselected)
          action haction).comp hprevious
      have hchosen : Measurable
          (fun history : History.FinitePairHistory Action Real (n + 1) =>
            (history lastIndex).1) :=
        measurable_fst.comp (measurable_pi_apply lastIndex)
      have hloss : Measurable
          (fun history : History.FinitePairHistory Action Real (n + 1) =>
            (history lastIndex).2) :=
        measurable_snd.comp (measurable_pi_apply lastIndex)
      have hincrement : Measurable
          (fun history : History.FinitePairHistory Action Real (n + 1) =>
            Exp3.importanceWeightedLoss
              (halfTsallisMinimizer arms harms (eta (n + 1))
                (sampledScheduledHalfTsallisHistoryScore arms harms eta n
                  (Exp3.previousPairHistory history)))
              (fun _ => (history lastIndex).2)
              (history lastIndex).1 action) :=
        Exp3.measurable_observedImportanceWeightedLoss
          (fun history =>
            halfTsallisMinimizer arms harms (eta (n + 1))
              (sampledScheduledHalfTsallisHistoryScore arms harms eta n
                (Exp3.previousPairHistory history)))
          (fun history => (history lastIndex).1)
          (fun history => (history lastIndex).2)
          action hprob hchosen hloss
      simpa [sampledScheduledHalfTsallisHistoryScore, lastIndex] using
        hscore.add hincrement

/-- Scheduled successor probabilities after the visible prefix through `n`. -/
noncomputable def sampledScheduledHalfTsallisHistoryDistribution
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (n : Nat) :
    History.FinitePairHistory Action Real n -> Action -> Real :=
  halfTsallisHistoryMinimizer arms harms (eta (n + 1))
    (sampledScheduledHalfTsallisHistoryScore arms harms eta n)

/-- Measurable finite-action source for one scheduled successor policy. -/
noncomputable def sampledScheduledHalfTsallisHistoryDistributionSource
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    Exp3.MeasurableFiniteActionDistribution arms
      (sampledScheduledHalfTsallisHistoryDistribution
        arms harms eta n) :=
  measurableFiniteActionDistribution_halfTsallisHistoryMinimizer
    arms harms (eta (n + 1))
    (sampledScheduledHalfTsallisHistoryScore arms harms eta n)
    (fun action haction =>
      (selector.round (n + 1)).measurable_selector n
        (sampledScheduledHalfTsallisHistoryScore arms harms eta n)
        (fun selected hselected =>
          measurable_sampledScheduledHalfTsallisHistoryScore
            arms harms eta selector n selected hselected)
        action haction)

/-- Stochastic finite-history algorithm generated by the scheduled recursive
score. -/
noncomputable def sampledScheduledHalfTsallisHistoryAlgorithm
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) :
    Thompson.HistoryAlgorithm Action Real where
  policy n := Exp3.finiteActionKernel arms
    (sampledScheduledHalfTsallisHistoryDistribution arms harms eta n)
    (sampledScheduledHalfTsallisHistoryDistributionSource
      arms harms eta selector n)
  policy_isMarkov n := Exp3.instFiniteActionKernelIsMarkovKernel
    arms (sampledScheduledHalfTsallisHistoryDistribution arms harms eta n)
      (sampledScheduledHalfTsallisHistoryDistributionSource
        arms harms eta selector n)
  initialAction := Exp3.finiteActionMeasure arms
    (initialHalfTsallisDistribution arms harms (eta 0))
  initialAction_isProbability := Exp3.finiteActionMeasure_isProbabilityMeasure
    arms (initialHalfTsallisDistribution arms harms (eta 0))
      (finiteActionDistribution_initialHalfTsallisDistribution
        arms harms (eta 0))

@[simp]
theorem sampledScheduledHalfTsallisHistoryAlgorithm_policy
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    (sampledScheduledHalfTsallisHistoryAlgorithm
      arms harms eta selector).policy n =
      Exp3.finiteActionKernel arms
        (sampledScheduledHalfTsallisHistoryDistribution arms harms eta n)
        (sampledScheduledHalfTsallisHistoryDistributionSource
          arms harms eta selector n) :=
  rfl

/-- Complete environment-indexed scheduled half-Tsallis trajectory. -/
noncomputable def sampledScheduledHalfTsallisTrajectoryKernel
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action] [Nonempty Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real) :
    Kernel Env ((n : Nat) -> Action × Real) :=
  Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
    (sampledScheduledHalfTsallisHistoryAlgorithm
      arms harms eta selector) environment

instance instSampledScheduledHalfTsallisTrajectoryKernelIsMarkov
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action] [Nonempty Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real) :
    IsMarkovKernel
      (sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector environment) := by
  unfold sampledScheduledHalfTsallisTrajectoryKernel
  infer_instance

/-- The successor action has its scheduled finite-action law conditional on
the visible pair-history prefix. -/
theorem sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real)
    (n : Nat) :
    condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 (n + 1)).1)
        (fun sample => Preorder.frestrictLe n sample.2)
        (prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
          arms harms eta selector environment) =ᵐ[
      (prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector environment).map
          (fun sample => Preorder.frestrictLe n sample.2)]
      Exp3.finiteActionKernel arms
        (sampledScheduledHalfTsallisHistoryDistribution arms harms eta n)
        (sampledScheduledHalfTsallisHistoryDistributionSource
          arms harms eta selector n) := by
  simpa [sampledScheduledHalfTsallisTrajectoryKernel,
    sampledScheduledHalfTsallisHistoryAlgorithm_policy] using
    (Thompson.canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action
      prior
      (sampledScheduledHalfTsallisHistoryAlgorithm
        arms harms eta selector)
      environment n)

/-- The scheduled conditional law after retaining the environment in the
visible history. -/
theorem sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real)
    (n : Nat) :
    condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 (n + 1)).1)
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.1, Preorder.frestrictLe n sample.2))
        (prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
          arms harms eta selector environment) =ᵐ[
      (prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector environment).map
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe n sample.2))]
      (Exp3.finiteActionKernel arms
        (sampledScheduledHalfTsallisHistoryDistribution arms harms eta n)
        (sampledScheduledHalfTsallisHistoryDistributionSource
          arms harms eta selector n)).comap
        (fun input : Env × History.FinitePairHistory Action Real n => input.2)
        (measurable_snd : Measurable
          (fun input : Env × History.FinitePairHistory Action Real n =>
            input.2)) := by
  simpa [sampledScheduledHalfTsallisTrajectoryKernel,
    sampledScheduledHalfTsallisHistoryAlgorithm_policy] using
    (Exp3.trajectoryMixture_condDistrib_action_given_environment_history prior
      (sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector environment)
      (Preorder.frestrictLe n) (Preorder.measurable_frestrictLe n)
      (fun trajectory => (trajectory (n + 1)).1)
      (measurable_fst.comp (measurable_pi_apply (n + 1)))
      ((sampledScheduledHalfTsallisHistoryAlgorithm
        arms harms eta selector).policy n)
      (fun env =>
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_map_history_action_eq_compProd
          (sampledScheduledHalfTsallisHistoryAlgorithm
            arms harms eta selector)
          environment env n))

end Tsallis
end BanditRLProof
