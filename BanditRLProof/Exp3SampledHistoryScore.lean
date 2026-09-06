import BanditRLProof.Exp3RecursiveTrajectory

/-!
# Sampled importance-weighted EXP3 history scores

This module closes the input-score boundary of `Exp3RecursiveTrajectory` for
real-valued observed losses.  The score at an inclusive finite history is the
previous score plus the importance-weighted loss of the newly observed pair.
The probability in that increment is exactly the exploration-mixed policy
computed from the preceding score and history prefix.

The resulting theorem constructs the concrete recursive EXP3 trajectory and
identifies every successor action's conditional law.  Expected-regret assembly
and parameter optimization remain downstream.
-/

namespace BanditRLProof
namespace Exp3

open MeasureTheory ProbabilityTheory

universe u w

/-- Remove the newest coordinate from an inclusive successor pair history. -/
def previousPairHistory {Action : Type u} {n : Nat}
    (history : History.FinitePairHistory Action Real (n + 1)) :
    History.FinitePairHistory Action Real n :=
  fun i => history
    ⟨i.1, Finset.mem_Iic.mpr
      ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩

theorem measurable_previousPairHistory
    {Action : Type u} [MeasurableSpace Action] {n : Nat} :
    Measurable
      (previousPairHistory (Action := Action) (n := n)) := by
  refine measurable_pi_lambda _ ?_
  intro i
  let oldIndex : Finset.Iic (n + 1) :=
    ⟨i.1, Finset.mem_Iic.mpr
      ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩
  exact measurable_pi_apply oldIndex

/--
Measurability of one importance-weighted coordinate when only the sampled
action and its scalar observed loss are available.
-/
theorem measurable_observedImportanceWeightedLoss
    {History : Type*} {Action : Type u}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (prob : History -> Action -> Real)
    (chosen : History -> Action) (observedLoss : History -> Real)
    (action : Action)
    (hprob : Measurable (fun history => prob history action))
    (hchosen : Measurable chosen) (hloss : Measurable observedLoss) :
    Measurable (fun history =>
      importanceWeightedLoss (prob history)
        (fun _ => observedLoss history) (chosen history) action) := by
  unfold importanceWeightedLoss
  refine Measurable.ite ?_ (hloss.div hprob) measurable_const
  simpa only [Set.mem_setOf_eq] using
    hchosen (measurableSet_singleton action)

/--
The cumulative sampled importance-weighted loss through an inclusive history.

At time zero the estimator uses the initial action law.  At time `n + 1`, it
uses the exploration-mixed law generated from the score on the prefix through
`n`, exactly matching `HistoryAlgorithm.policy n`.
-/
noncomputable def sampledHistoryScore
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) :
    (n : Nat) -> History.FinitePairHistory Action Real n -> Action -> Real
  | 0, history, action =>
      importanceWeightedLoss
        (initialExploredDistribution arms eta gamma)
        (fun _ => (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2)
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 action
  | n + 1, history, action =>
      let previous := previousPairHistory history
      sampledHistoryScore arms eta gamma n previous action +
        importanceWeightedLoss
          (exploredHistoryDistribution arms eta gamma
            (sampledHistoryScore arms eta gamma n) previous)
          (fun _ =>
            (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 action

@[simp]
theorem sampledHistoryScore_zero
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (history : History.FinitePairHistory Action Real 0)
    (action : Action) :
    sampledHistoryScore arms eta gamma 0 history action =
      importanceWeightedLoss
        (initialExploredDistribution arms eta gamma)
        (fun _ => (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2)
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 action :=
  rfl

@[simp]
theorem sampledHistoryScore_succ
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (n : Nat)
    (history : History.FinitePairHistory Action Real (n + 1))
    (action : Action) :
    sampledHistoryScore arms eta gamma (n + 1) history action =
      sampledHistoryScore arms eta gamma n
          (previousPairHistory history) action +
        importanceWeightedLoss
          (exploredHistoryDistribution arms eta gamma
            (sampledHistoryScore arms eta gamma n)
            (previousPairHistory history))
          (fun _ =>
            (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 action :=
  rfl

theorem measurable_sampledHistoryScore
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) :
    forall n action, action ∈ arms ->
      Measurable (fun history : History.FinitePairHistory Action Real n =>
        sampledHistoryScore arms eta gamma n history action) := by
  intro n
  induction n with
  | zero =>
      intro action _haction
      let zeroIndex : Finset.Iic 0 :=
        ⟨0, Finset.mem_Iic.mpr le_rfl⟩
      have hchosen : Measurable
          (fun history : History.FinitePairHistory Action Real 0 =>
            (history zeroIndex).1) :=
        measurable_fst.comp (measurable_pi_apply zeroIndex)
      have hloss : Measurable
          (fun history : History.FinitePairHistory Action Real 0 =>
            (history zeroIndex).2) :=
        measurable_snd.comp (measurable_pi_apply zeroIndex)
      simpa [sampledHistoryScore, zeroIndex] using
        (measurable_observedImportanceWeightedLoss
          (fun _history : History.FinitePairHistory Action Real 0 =>
            initialExploredDistribution arms eta gamma)
          (fun history => (history zeroIndex).1)
          (fun history => (history zeroIndex).2)
          action measurable_const hchosen hloss)
  | succ n ih =>
      intro action haction
      let lastIndex : Finset.Iic (n + 1) :=
        ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
      have hprevious : Measurable
          (previousPairHistory (Action := Action) (n := n)) :=
        measurable_previousPairHistory
      have hscore : Measurable
          (fun history : History.FinitePairHistory Action Real (n + 1) =>
            sampledHistoryScore arms eta gamma n
              (previousPairHistory history) action) :=
        (ih action haction).comp hprevious
      have hprob : Measurable
          (fun history : History.FinitePairHistory Action Real (n + 1) =>
            exploredHistoryDistribution arms eta gamma
              (sampledHistoryScore arms eta gamma n)
              (previousPairHistory history) action) := by
        exact
          (measurable_exploredHistoryDistribution arms eta gamma
            (sampledHistoryScore arms eta gamma n)
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
            importanceWeightedLoss
              (exploredHistoryDistribution arms eta gamma
                (sampledHistoryScore arms eta gamma n)
                (previousPairHistory history))
              (fun _ => (history lastIndex).2)
              (history lastIndex).1 action) :=
        measurable_observedImportanceWeightedLoss
          (fun history =>
            exploredHistoryDistribution arms eta gamma
              (sampledHistoryScore arms eta gamma n)
              (previousPairHistory history))
          (fun history => (history lastIndex).1)
          (fun history => (history lastIndex).2)
          action hprob hchosen hloss
      simpa [sampledHistoryScore, lastIndex] using hscore.add hincrement

/-- The concrete sampled score satisfies the generic measurable-score API. -/
theorem measurableFiniteHistoryScore_sampledHistoryScore
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) :
    MeasurableFiniteHistoryScore arms
      (sampledHistoryScore arms eta gamma) where
  measurable_score :=
    measurable_sampledHistoryScore arms eta gamma

/-- Concrete exploration-mixed probabilities generated by sampled losses. -/
noncomputable def sampledHistoryDistribution
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (n : Nat) :
    History.FinitePairHistory Action Real n -> Action -> Real :=
  exploredHistoryDistribution arms eta gamma
    (sampledHistoryScore arms eta gamma n)

theorem sampledHistoryDistribution_floor
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_le_one : gamma <= 1)
    (n : Nat) (history : History.FinitePairHistory Action Real n)
    (action : Action) :
    gamma / (arms.card : Real) <=
      sampledHistoryDistribution arms eta gamma n history action := by
  exact exploredHistoryDistribution_floor arms harms eta gamma
    (sampledHistoryScore arms eta gamma n) hgamma_le_one history action

/-- The concrete stochastic history algorithm for sampled-loss EXP3. -/
noncomputable def sampledImportanceWeightedHistoryAlgorithm
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1) :
    Thompson.HistoryAlgorithm Action Real :=
  exploredHistoryAlgorithm arms harms eta gamma
    (sampledHistoryScore arms eta gamma)
    (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
    hgamma_nonneg hgamma_le_one

@[simp]
theorem sampledImportanceWeightedHistoryAlgorithm_policy
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (n : Nat) :
    (sampledImportanceWeightedHistoryAlgorithm arms harms eta gamma
      hgamma_nonneg hgamma_le_one).policy n =
      finiteActionKernel arms
        (sampledHistoryDistribution arms eta gamma n)
        (exploredHistoryDistributionSource arms harms eta gamma
          (sampledHistoryScore arms eta gamma)
          (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
          hgamma_nonneg hgamma_le_one n) := by
  rfl

/-- Complete recursive sampled-loss EXP3 trajectory kernel. -/
noncomputable def sampledImportanceWeightedTrajectoryKernel
    {Env : Type w} {Action : Type u}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action] [Nonempty Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real) :
    Kernel Env ((n : Nat) -> Action × Real) :=
  exploredTrajectoryKernel arms harms eta gamma
    (sampledHistoryScore arms eta gamma)
    (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
    hgamma_nonneg hgamma_le_one environment

instance instSampledImportanceWeightedTrajectoryKernelIsMarkov
    {Env : Type w} {Action : Type u}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action] [Nonempty Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real) :
    IsMarkovKernel
      (sampledImportanceWeightedTrajectoryKernel arms harms eta gamma
        hgamma_nonneg hgamma_le_one environment) := by
  unfold sampledImportanceWeightedTrajectoryKernel
  infer_instance

/--
Every successor action of the concrete sampled-loss EXP3 trajectory has the
exploration-mixed law generated from its recursively accumulated
importance-weighted score.
-/
theorem sampledImportanceWeightedTrajectoryMeasure_condDistrib_action
    {Env : Type w} {Action : Type u}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real)
    (n : Nat) :
    condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 (n + 1)).1)
        (fun sample => Preorder.frestrictLe n sample.2)
        (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_nonneg hgamma_le_one environment) =ᵐ[
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        eta gamma hgamma_nonneg hgamma_le_one environment).map
          (fun sample => Preorder.frestrictLe n sample.2)]
      finiteActionKernel arms
        (sampledHistoryDistribution arms eta gamma n)
        (exploredHistoryDistributionSource arms harms eta gamma
          (sampledHistoryScore arms eta gamma)
          (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
          hgamma_nonneg hgamma_le_one n) := by
  simpa [sampledImportanceWeightedTrajectoryKernel,
    sampledHistoryDistribution] using
    (exploredTrajectoryMeasure_condDistrib_action prior arms harms eta gamma
      (sampledHistoryScore arms eta gamma)
      (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
      hgamma_nonneg hgamma_le_one environment n)

end Exp3
end BanditRLProof
