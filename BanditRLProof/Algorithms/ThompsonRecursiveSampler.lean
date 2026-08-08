import BanditRLProof.Algorithms.ThompsonMeasurableTrajectory
import Mathlib.Probability.Distributions.Uniform

/-!
# Globally coupled Thompson trajectories

This module closes the gap between a separately adjoined one-step posterior
sampler and the action coordinate of one recursive trajectory.  The Thompson
policy is defined non-circularly from a fixed reference trajectory, following
the uniform-reference design of LML's `TS.policy`.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v w x

namespace BanditRLProof
namespace Thompson

/-- Uniform probability measure on a nonempty finite action space. -/
noncomputable def uniformActionMeasure
    (Action : Type u) [Fintype Action] [Nonempty Action]
    [MeasurableSpace Action] : Measure Action :=
  (PMF.uniformOfFintype Action).toMeasure

instance instUniformActionMeasureIsProbabilityMeasure
    (Action : Type u) [Fintype Action] [Nonempty Action]
    [MeasurableSpace Action] :
    IsProbabilityMeasure (uniformActionMeasure Action) := by
  unfold uniformActionMeasure
  infer_instance

/-- Every measure on a finite space is dominated by its uniform measure. -/
theorem absolutelyContinuous_uniformActionMeasure
    {Action : Type u} [Fintype Action] [Nonempty Action]
    [MeasurableSpace Action] (mu : Measure Action) :
    mu ≪ uniformActionMeasure Action := by
  apply Measure.AbsolutelyContinuous.mk
  intro event hevent huniform
  by_cases hempty : event = ∅
  · simp [hempty]
  letI : Fintype event := Fintype.ofFinite event
  have heventNonempty : event.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  have hcard : (Fintype.card event : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (Set.nonempty_coe_sort.mpr heventNonempty)).ne'
  have hpositive :
      0 < (Fintype.card event : ENNReal) / Fintype.card Action :=
    ENNReal.div_pos hcard (ENNReal.natCast_ne_top _)
  rw [← PMF.toMeasure_uniformOfFintype_apply event hevent] at hpositive
  unfold uniformActionMeasure at huniform
  rw [huniform] at hpositive
  exact (lt_irrefl 0 hpositive).elim

/-- History-independent uniform reference algorithm. -/
noncomputable def uniformHistoryAlgorithm
    (Action : Type u) (Reward : Type v)
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace Action] [MeasurableSpace Reward] :
    HistoryAlgorithm Action Reward where
  initialAction := uniformActionMeasure Action
  policy n := ProbabilityTheory.Kernel.const
    (History.FinitePairHistory Action Reward n) (uniformActionMeasure Action)

/-- Any history algorithm is absolutely continuous with respect to uniform. -/
theorem historyAlgorithmAbsolutelyContinuous_uniform
    {Action : Type u} {Reward : Type v}
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward) :
    HistoryAlgorithmAbsolutelyContinuous algorithm
      (uniformHistoryAlgorithm Action Reward) where
  initialAction := absolutelyContinuous_uniformActionMeasure
    algorithm.initialAction
  policy := fun n history => by
    simpa only [uniformHistoryAlgorithm, ProbabilityTheory.Kernel.const_apply]
      using absolutelyContinuous_uniformActionMeasure (algorithm.policy n history)

/--
Mixing environment-indexed trajectory laws preserves a common conditional
action kernel.  This is the generic measure transport needed to turn
pointwise trajectory laws into one global recursive process law.
-/
theorem trajectoryMixture_map_history_action_eq_compProd
    {Env : Type u} {Omega : Type v} {History : Type w} {Action : Type x}
    [MeasurableSpace Env] [MeasurableSpace Omega]
    [MeasurableSpace History] [MeasurableSpace Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (trajectory : ProbabilityTheory.Kernel Env Omega)
    [ProbabilityTheory.IsMarkovKernel trajectory]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy]
    (hlaw : forall env,
      (trajectory env).map (fun omega => (history omega, action omega)) =
        (trajectory env).map history ⊗ₘ policy) :
    (prior ⊗ₘ trajectory).map
        (fun sample => (history sample.2, action sample.2)) =
      (prior ⊗ₘ trajectory).map (history ∘ Prod.snd) ⊗ₘ policy := by
  apply Measure.ext_prod
  intro historyEvent actionEvent hhistoryEvent hactionEvent
  let pairMap : Omega -> History × Action :=
    fun omega => (history omega, action omega)
  let globalPairMap : Env × Omega -> History × Action :=
    fun sample => pairMap sample.2
  let globalHistory : Env × Omega -> History := history ∘ Prod.snd
  have hpairMap : Measurable pairMap := hhistory.prodMk haction
  have hglobalPairMap : Measurable globalPairMap :=
    hpairMap.comp measurable_snd
  have hglobalHistory : Measurable globalHistory :=
    hhistory.comp measurable_snd
  have hpairEvent :
      MeasurableSet (pairMap ⁻¹' (historyEvent ×ˢ actionEvent)) :=
    hpairMap (hhistoryEvent.prod hactionEvent)
  have hpreimage :
      globalPairMap ⁻¹' (historyEvent ×ˢ actionEvent) =
        Set.univ ×ˢ (pairMap ⁻¹' (historyEvent ×ˢ actionEvent)) := by
    ext sample
    simp [globalPairMap, pairMap]
  have hpointwise (env : Env) :
      trajectory env (pairMap ⁻¹' (historyEvent ×ˢ actionEvent)) =
        ∫⁻ h in historyEvent, policy h actionEvent
          ∂(trajectory env).map history := by
    rw [← Measure.map_apply hpairMap (hhistoryEvent.prod hactionEvent),
      hlaw env, Measure.compProd_apply_prod hhistoryEvent hactionEvent]
  rw [Measure.map_apply hglobalPairMap (hhistoryEvent.prod hactionEvent),
    hpreimage, Measure.compProd_apply_prod MeasurableSet.univ hpairEvent]
  simp_rw [hpointwise]
  simp_rw [MeasureTheory.setLIntegral_map hhistoryEvent
    (policy.measurable_coe hactionEvent) hhistory]
  rw [Measure.compProd_apply_prod hhistoryEvent hactionEvent,
    MeasureTheory.setLIntegral_map hhistoryEvent
      (policy.measurable_coe hactionEvent) hglobalHistory]
  have hhistoryPreimage :
      globalHistory ⁻¹' historyEvent =
        Set.univ ×ˢ (history ⁻¹' historyEvent) := by
    ext sample
    simp [globalHistory]
  rw [hhistoryPreimage]
  simpa only [globalHistory, Function.comp_apply] using
    (Measure.setLIntegral_compProd
      (((policy.measurable_coe hactionEvent).comp hhistory).comp measurable_snd)
      MeasurableSet.univ (hhistory hhistoryEvent)).symm

/-- Conditional-law form of `trajectoryMixture_map_history_action_eq_compProd`. -/
theorem trajectoryMixture_condDistrib_action
    {Env : Type u} {Omega : Type v} {History : Type w} {Action : Type x}
    [MeasurableSpace Env] [MeasurableSpace Omega]
    [MeasurableSpace History]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (trajectory : ProbabilityTheory.Kernel Env Omega)
    [ProbabilityTheory.IsMarkovKernel trajectory]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy]
    (hlaw : forall env,
      (trajectory env).map (fun omega => (history omega, action omega)) =
        (trajectory env).map history ⊗ₘ policy) :
    ProbabilityTheory.condDistrib (action ∘ Prod.snd) (history ∘ Prod.snd)
        (prior ⊗ₘ trajectory) =ᵐ[(prior ⊗ₘ trajectory).map
          (history ∘ Prod.snd)] policy := by
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hhistory.comp measurable_snd) (haction.comp measurable_snd)
  exact trajectoryMixture_map_history_action_eq_compProd
    prior trajectory history hhistory action haction policy hlaw

/-- The visible action marginal of each fixed-environment successor law. -/
theorem canonicalMeasurableEnvironmentTrajectoryKernel_map_history_action_eq_compProd
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (env : Env) (n : Nat) :
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
        (fun trajectory =>
          (Preorder.frestrictLe n trajectory, (trajectory (n + 1)).1)) =
      (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
          (Preorder.frestrictLe n) ⊗ₘ algorithm.policy n := by
  calc
    _ = ((canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
          (fun trajectory =>
            (Preorder.frestrictLe n trajectory, trajectory (n + 1)))).map
          (Prod.map id Prod.fst) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
    _ = ((canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
          (Preorder.frestrictLe n) ⊗ₘ
        historyStepKernel algorithm (environment.at env) n).map
          (Prod.map id Prod.fst) := by
            rw [canonicalMeasurableEnvironmentTrajectoryKernel_map_prefix_next_eq_compProd]
    _ = (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
          (Preorder.frestrictLe n) ⊗ₘ
        (historyStepKernel algorithm (environment.at env) n).map Prod.fst := by
            rw [Measure.compProd_map measurable_fst]
    _ = _ := by rw [historyStepKernel_map_fst]

/--
The next action coordinate of the global prior/trajectory measure has the
algorithm policy as its conditional law given the visible finite history.
-/
theorem canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          (sample.2 (n + 1)).1)
        (fun sample => Preorder.frestrictLe n sample.2)
        (prior ⊗ₘ
          canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment) =ᵐ[
      (prior ⊗ₘ
        canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment).map
          (fun sample => Preorder.frestrictLe n sample.2)]
      algorithm.policy n := by
  exact trajectoryMixture_condDistrib_action
    prior (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment)
    (Preorder.frestrictLe n) (Preorder.measurable_frestrictLe n)
    (fun trajectory => (trajectory (n + 1)).1)
    (measurable_fst.comp (measurable_pi_apply (n + 1)))
    (algorithm.policy n)
    (canonicalMeasurableEnvironmentTrajectoryKernel_map_history_action_eq_compProd
      algorithm environment · n)

/--
Expose the posterior-invariance conclusion of the conditional process-density
route without adjoining a fresh action sampler.
-/
theorem finitePairReferencePosterior_ae_eq_condDistrib_of_conditionalProcessSource
    {Omega : Type u} {OmegaRef : Type v}
    {Env : Type w} {Action : Type x} {Reward : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (source : ConditionalHistoryAlgorithmDensitySource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment)
    (n : Nat) :
    let actualHistory := fun omega => History.finitePairHistoryOfTrace
      (action omega) (reward omega) n
    let referenceHistory := fun omega => History.finitePairHistoryOfTrace
      (referenceAction omega) (referenceReward omega) n
    (referencePosterior referenceMu referenceEnv referenceHistory
      source.measurable_referenceEnv
      (History.measurable_finitePairHistoryOfTrace
        referenceAction referenceReward source.measurable_referenceAction
          source.measurable_referenceReward n)).kernel =ᵐ[mu.map actualHistory]
      ProbabilityTheory.condDistrib env actualHistory mu := by
  dsimp only
  let actualHistory := fun omega => History.finitePairHistoryOfTrace
    (action omega) (reward omega) n
  let referenceHistory := fun omega => History.finitePairHistoryOfTrace
    (referenceAction omega) (referenceReward omega) n
  have hactualHistory : Measurable actualHistory :=
    History.measurable_finitePairHistoryOfTrace
      action reward source.measurable_action source.measurable_reward n
  have hreferenceHistory : Measurable referenceHistory :=
    History.measurable_finitePairHistoryOfTrace
      referenceAction referenceReward source.measurable_referenceAction
        source.measurable_referenceReward n
  let posteriorSource :=
    algorithmDensityPosteriorSource_of_condDistrib_history_withDensity
      mu env actualHistory source.measurable_env hactualHistory
      referenceMu referenceEnv referenceHistory source.measurable_referenceEnv
      hreferenceHistory (historyDensity algorithm referenceAlgorithm n)
      (measurable_historyDensity algorithm referenceAlgorithm n)
      source.env_map_eq
      (condDistrib_finitePairHistory_eq_withDensity_of_conditionalProcessSource
        mu env action reward referenceMu referenceEnv referenceAction
          referenceReward algorithm referenceAlgorithm feedbackEnvironment source n)
  exact referencePosterior_ae_eq_condDistrib_of_algorithmDensitySource
    mu env actualHistory source.measurable_env referenceMu referenceEnv
    referenceHistory source.measurable_referenceEnv hreferenceHistory
    posteriorSource

/--
Thompson's non-circular history algorithm: every policy is the posterior under
one fixed reference trajectory, mapped through `bestAction`.
-/
noncomputable def referencePosteriorHistoryAlgorithm
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    [MeasurableSpace Reward] [Nonempty Action] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    HistoryAlgorithm Action Reward where
  initialAction := prior.map bestAction
  initialAction_isProbability :=
    MeasureTheory.Measure.isProbabilityMeasure_map hbestAction.aemeasurable
  policy n :=
    referenceActionKernel
      (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
        referenceAlgorithm environment)
      Prod.fst
      (fun sample => History.finitePairHistoryOfTrace
        (environmentTrajectoryAction sample)
        (environmentTrajectoryReward sample) n)
      measurable_fst
      (History.measurable_finitePairHistoryOfTrace
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply n)
      bestAction hbestAction

@[simp]
theorem referencePosteriorHistoryAlgorithm_initialAction
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    [MeasurableSpace Reward] [Nonempty Action] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    (referencePosteriorHistoryAlgorithm prior referenceAlgorithm environment
      bestAction hbestAction).initialAction = prior.map bestAction := rfl

@[simp]
theorem referencePosteriorHistoryAlgorithm_policy
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    [MeasurableSpace Reward] [Nonempty Action] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (n : Nat) :
    (referencePosteriorHistoryAlgorithm prior referenceAlgorithm environment
      bestAction hbestAction).policy n =
      referenceActionKernel
        (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
          referenceAlgorithm environment)
        Prod.fst
        (fun sample => History.finitePairHistoryOfTrace
          (environmentTrajectoryAction sample)
          (environmentTrajectoryReward sample) n)
        measurable_fst
        (History.measurable_finitePairHistoryOfTrace
          environmentTrajectoryAction environmentTrajectoryReward
          measurable_environmentTrajectoryAction_apply
          measurable_environmentTrajectoryReward_apply n)
        bestAction hbestAction := rfl

/--
Probability matching for the action coordinate of one globally generated
Thompson trajectory.  Unlike the earlier finite-prefix sampler endpoint, the
next action here is the actual successor coordinate of the same recursive
trajectory whose history appears in the conditioning variable.

The remaining support contract is the standard algorithm-density condition
against the fixed reference algorithm.  A finite uniform reference discharges
that contract in the downstream specialization.
-/
theorem referencePosteriorHistoryAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (absolutelyContinuous : HistoryAlgorithmAbsolutelyContinuous
      (referencePosteriorHistoryAlgorithm prior referenceAlgorithm environment
        bestAction hbestAction)
      referenceAlgorithm)
    (n : Nat) :
    let algorithm := referencePosteriorHistoryAlgorithm prior referenceAlgorithm
      environment bestAction hbestAction
    let trajectoryKernel :=
      canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    let actualMeasure := prior ⊗ₘ trajectoryKernel
    let actualHistory := fun sample => History.finitePairHistoryOfTrace
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample) n
    let nextAction := fun sample => environmentTrajectoryAction sample (n + 1)
    ProbabilityTheory.condDistrib nextAction actualHistory actualMeasure =ᵐ[
      actualMeasure.map actualHistory]
      ProbabilityTheory.condDistrib (bestAction ∘ Prod.fst)
        actualHistory actualMeasure := by
  dsimp only
  let algorithm := referencePosteriorHistoryAlgorithm prior referenceAlgorithm
    environment bestAction hbestAction
  let trajectoryKernel :=
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  let referenceTrajectoryKernel :=
    canonicalMeasurableEnvironmentTrajectoryKernel referenceAlgorithm environment
  let actualMeasure := prior ⊗ₘ trajectoryKernel
  let referenceMeasure := prior ⊗ₘ referenceTrajectoryKernel
  let actualHistory := fun sample : Env × ((k : Nat) -> Action × Reward) =>
    History.finitePairHistoryOfTrace
    (environmentTrajectoryAction sample)
    (environmentTrajectoryReward sample) n
  let referenceHistory := fun sample : Env × ((k : Nat) -> Action × Reward) =>
    History.finitePairHistoryOfTrace
    (environmentTrajectoryAction sample)
    (environmentTrajectoryReward sample) n
  let nextAction := fun sample : Env × ((k : Nat) -> Action × Reward) =>
    environmentTrajectoryAction sample (n + 1)
  have hactualHistory : Measurable actualHistory :=
    History.measurable_finitePairHistoryOfTrace
      environmentTrajectoryAction environmentTrajectoryReward
      measurable_environmentTrajectoryAction_apply
      measurable_environmentTrajectoryReward_apply n
  have hreferenceHistory : Measurable referenceHistory :=
    History.measurable_finitePairHistoryOfTrace
      environmentTrajectoryAction environmentTrajectoryReward
      measurable_environmentTrajectoryAction_apply
      measurable_environmentTrajectoryReward_apply n
  have hnextAction : Measurable nextAction :=
    measurable_environmentTrajectoryAction_apply (n + 1)
  have htrajectoryKernel : forall env,
      trajectoryKernel env =
        canonicalHistoryTrajectoryMeasure algorithm (environment.at env) :=
    fun env => canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical
      algorithm environment env
  have hreferenceTrajectoryKernel : forall env,
      referenceTrajectoryKernel env =
        canonicalHistoryTrajectoryMeasure referenceAlgorithm
          (environment.at env) :=
    fun env => canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical
      referenceAlgorithm environment env
  let splitSource :=
    conditionalHistoryAlgorithmDensitySplitSource_of_canonicalTrajectoryKernels
      prior algorithm referenceAlgorithm environment.at trajectoryKernel
      referenceTrajectoryKernel htrajectoryKernel hreferenceTrajectoryKernel
      absolutelyContinuous
  let processSource := conditionalHistoryAlgorithmDensitySource_of_split
    actualMeasure Prod.fst environmentTrajectoryAction
    environmentTrajectoryReward referenceMeasure Prod.fst
    environmentTrajectoryAction environmentTrajectoryReward algorithm
    referenceAlgorithm environment.at splitSource
  let posterior := referencePosterior referenceMeasure Prod.fst referenceHistory
    measurable_fst hreferenceHistory
  have hposterior : posterior.kernel =ᵐ[actualMeasure.map actualHistory]
      ProbabilityTheory.condDistrib Prod.fst actualHistory actualMeasure := by
    exact finitePairReferencePosterior_ae_eq_condDistrib_of_conditionalProcessSource
      actualMeasure Prod.fst environmentTrajectoryAction
      environmentTrajectoryReward referenceMeasure Prod.fst
      environmentTrajectoryAction environmentTrajectoryReward algorithm
      referenceAlgorithm environment.at processSource n
  have haction :
      ProbabilityTheory.condDistrib nextAction actualHistory actualMeasure =ᵐ[
        actualMeasure.map actualHistory] posterior.kernel.map bestAction := by
    simpa only [algorithm, trajectoryKernel, actualMeasure, actualHistory,
      nextAction, posterior, referenceMeasure, referenceTrajectoryKernel,
      referencePosteriorHistoryAlgorithm_policy, referenceActionKernel,
      History.finitePairHistoryOfTrace, environmentTrajectoryAction,
      environmentTrajectoryReward, Function.comp_apply] using
      (canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action
        prior algorithm environment n)
  exact condDistrib_action_ae_eq_bestAction_of_posteriorMap
    actualMeasure Prod.fst actualHistory nextAction posterior bestAction
    hbestAction measurable_fst hactualHistory hnextAction haction hposterior

/--
Concrete finite-action Thompson algorithm using one uniform reference process.
The definition is non-circular: its posterior policy is computed from the
uniform algorithm's trajectory, not from the Thompson trajectory being built.
-/
noncomputable def uniformReferenceThompsonAlgorithm
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [Fintype Action] [Nonempty Action]
    [MeasurableSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    HistoryAlgorithm Action Reward :=
  referencePosteriorHistoryAlgorithm prior
    (uniformHistoryAlgorithm Action Reward) environment bestAction hbestAction

/--
Premise-free finite-action probability matching on the actual globally
recursive Thompson trajectory.  Uniform full support discharges every
algorithm-density absolute-continuity obligation internally.
-/
theorem uniformReferenceThompsonAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (n : Nat) :
    let algorithm := uniformReferenceThompsonAlgorithm prior environment
      bestAction hbestAction
    let trajectoryKernel :=
      canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    let actualMeasure := prior ⊗ₘ trajectoryKernel
    let actualHistory := fun sample => History.finitePairHistoryOfTrace
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample) n
    let nextAction := fun sample => environmentTrajectoryAction sample (n + 1)
    ProbabilityTheory.condDistrib nextAction actualHistory actualMeasure =ᵐ[
      actualMeasure.map actualHistory]
      ProbabilityTheory.condDistrib (bestAction ∘ Prod.fst)
        actualHistory actualMeasure := by
  exact
    referencePosteriorHistoryAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
      prior (uniformHistoryAlgorithm Action Reward) environment bestAction
      hbestAction
      (historyAlgorithmAbsolutelyContinuous_uniform
        (uniformReferenceThompsonAlgorithm prior environment
          bestAction hbestAction))
      n

end Thompson
end BanditRLProof
