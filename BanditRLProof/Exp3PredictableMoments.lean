import BanditRLProof.Exp3PredictableAdversary
import BanditRLProof.ExpectationBochnerSums

/-!
# Predictable EXP3 feedback and moment laws

This file transports the fixed-environment canonical trajectory law through an
environment prior.  The resulting global joint law retains the latent
environment in the conditioning history, which is the law surface needed to
identify predictable feedback coordinates and their roundwise moments.
-/

open MeasureTheory ProbabilityTheory

universe u v w x

namespace BanditRLProof
namespace Exp3

/--
Mixing fixed-environment trajectory laws preserves a history-dependent output
kernel when the conditioning variable retains the environment coordinate.
-/
theorem trajectoryMixture_map_environment_history_output_eq_compProd
    {Env : Type u} {Omega : Type v} {History : Type w} {Output : Type x}
    [MeasurableSpace Env] [MeasurableSpace Omega]
    [MeasurableSpace History] [MeasurableSpace Output]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (trajectory : Kernel Env Omega) [IsMarkovKernel trajectory]
    (history : Omega -> History) (hhistory : Measurable history)
    (output : Omega -> Output) (houtput : Measurable output)
    (outputKernel : Kernel (Env × History) Output)
    [IsMarkovKernel outputKernel]
    (hlaw : forall env,
      (trajectory env).map (fun omega => (history omega, output omega)) =
        (trajectory env).map history ⊗ₘ
          outputKernel.comap (fun h => (env, h))
            (measurable_const.prodMk measurable_id)) :
    (prior ⊗ₘ trajectory).map
        (fun sample : Env × Omega =>
          ((sample.1, history sample.2), output sample.2)) =
      (prior ⊗ₘ trajectory).map
          (fun sample : Env × Omega => (sample.1, history sample.2)) ⊗ₘ
        outputKernel := by
  apply Measure.ext_prod
  intro environmentHistoryEvent outputEvent hEnvironmentHistoryEvent hOutputEvent
  let pairMap : Omega -> History × Output :=
    fun omega => (history omega, output omega)
  let globalPairMap : Env × Omega -> (Env × History) × Output :=
    fun sample => ((sample.1, history sample.2), output sample.2)
  let globalHistory : Env × Omega -> Env × History :=
    fun sample => (sample.1, history sample.2)
  have hpairMap : Measurable pairMap := hhistory.prodMk houtput
  have hglobalPairMap : Measurable globalPairMap :=
    (measurable_fst.prodMk (hhistory.comp measurable_snd)).prodMk
      (houtput.comp measurable_snd)
  have hglobalHistory : Measurable globalHistory :=
    measurable_fst.prodMk (hhistory.comp measurable_snd)
  rw [Measure.map_apply hglobalPairMap
      (hEnvironmentHistoryEvent.prod hOutputEvent),
    Measure.compProd_apply_prod hEnvironmentHistoryEvent hOutputEvent]
  conv_rhs =>
    change ∫⁻ a in environmentHistoryEvent,
      outputKernel a outputEvent
        ∂Measure.map globalHistory (prior ⊗ₘ trajectory)
    rw [MeasureTheory.setLIntegral_map hEnvironmentHistoryEvent
      (outputKernel.measurable_coe hOutputEvent) hglobalHistory]
  have hhistorySection (env : Env) : MeasurableSet
      {h : History | (env, h) ∈ environmentHistoryEvent} :=
    hEnvironmentHistoryEvent.preimage
      (measurable_const.prodMk measurable_id)
  have hsection (env : Env) : MeasurableSet
      {omega : Omega | (env, history omega) ∈ environmentHistoryEvent} :=
    (hhistorySection env).preimage hhistory
  let integrand : Env × Omega -> ENNReal :=
    fun sample => outputKernel (sample.1, history sample.2) outputEvent
  have hintegrand : Measurable integrand :=
    (outputKernel.measurable_coe hOutputEvent).comp
      (measurable_fst.prodMk (hhistory.comp measurable_snd))
  have hglobalHistoryEvent :
      MeasurableSet (globalHistory ⁻¹' environmentHistoryEvent) :=
    hglobalHistory hEnvironmentHistoryEvent
  conv_rhs =>
    change ∫⁻ sample in globalHistory ⁻¹' environmentHistoryEvent,
      integrand sample ∂(prior ⊗ₘ trajectory)
    rw [← MeasureTheory.lintegral_indicator hglobalHistoryEvent,
      Measure.lintegral_compProd
        (hintegrand.indicator hglobalHistoryEvent)]
  rw [Measure.compProd_apply]
  · apply lintegral_congr
    intro env
    have hpointwise :
        trajectory env
            (pairMap ⁻¹' ({h : History | (env, h) ∈ environmentHistoryEvent} ×ˢ
              outputEvent)) =
          ∫⁻ h in {h : History | (env, h) ∈ environmentHistoryEvent},
            outputKernel (env, h) outputEvent ∂(trajectory env).map history := by
      rw [← Measure.map_apply hpairMap
          ((hhistorySection env).prod hOutputEvent),
        hlaw env,
        Measure.compProd_apply_prod (hhistorySection env) hOutputEvent]
      simp only [Kernel.coe_comap, Function.comp_apply]
    have hpreimage :
        (Prod.mk env) ⁻¹'
            (globalPairMap ⁻¹'
              (environmentHistoryEvent ×ˢ outputEvent)) =
          pairMap ⁻¹' ({h : History | (env, h) ∈ environmentHistoryEvent} ×ˢ
            outputEvent) := by
      ext omega
      simp [pairMap, globalPairMap]
    have hmap :
        (∫⁻ h in {h : History | (env, h) ∈ environmentHistoryEvent},
            outputKernel (env, h) outputEvent
            ∂(trajectory env).map history) =
          ∫⁻ omega in {omega : Omega |
              (env, history omega) ∈ environmentHistoryEvent},
            outputKernel (env, history omega) outputEvent
            ∂trajectory env := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.setLIntegral_map (hhistorySection env)
          ((outputKernel.measurable_coe hOutputEvent).comp
            (measurable_const.prodMk measurable_id)) hhistory
          (μ := trajectory env))
    rw [hpreimage, hpointwise, hmap]
    conv_rhs =>
      change ∫⁻ omega,
        (globalHistory ⁻¹' environmentHistoryEvent).indicator integrand
          (env, omega) ∂trajectory env
      rw [show
          (fun omega =>
            (globalHistory ⁻¹' environmentHistoryEvent).indicator integrand
              (env, omega)) =
            {omega : Omega |
              (env, history omega) ∈ environmentHistoryEvent}.indicator
                (fun omega =>
                  outputKernel (env, history omega) outputEvent) by
          funext omega
          by_cases hmem :
              (env, history omega) ∈ environmentHistoryEvent <;>
            simp [globalHistory, integrand, Set.indicator, hmem]]
      rw [MeasureTheory.lintegral_indicator (hsection env)]
  · exact hglobalPairMap
      (hEnvironmentHistoryEvent.prod hOutputEvent)

/--
The canonical measurable trajectory, mixed over an environment prior, has the
joint law obtained by adjoining one global measurable history-step kernel to
the retained environment/prefix history.
-/
theorem canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_prefix_next_eq_compProd
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : Thompson.HistoryAlgorithm Action Reward)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Reward)
    (n : Nat) :
    (prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm environment).map
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          ((sample.1, Preorder.frestrictLe n sample.2), sample.2 (n + 1))) =
      (prior ⊗ₘ
          Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
            algorithm environment).map
          (fun sample : Env × ((k : Nat) -> Action × Reward) =>
            (sample.1, Preorder.frestrictLe n sample.2)) ⊗ₘ
        Thompson.measurableEnvironmentHistoryStepKernel
          algorithm environment n := by
  apply trajectoryMixture_map_environment_history_output_eq_compProd
    prior
    (Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
      algorithm environment)
    (Preorder.frestrictLe n) (Preorder.measurable_frestrictLe n)
    (fun trajectory => trajectory (n + 1)) (measurable_pi_apply (n + 1))
    (Thompson.measurableEnvironmentHistoryStepKernel algorithm environment n)
  intro env
  rw [Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_map_prefix_next_eq_compProd]
  congr 1
  ext history event hevent
  rw [Kernel.comap_apply,
    Thompson.measurableEnvironmentHistoryStepKernel_apply]

/--
Conditional on the latent environment and the preceding finite pair history,
the next canonical trajectory pair follows the global measurable history-step
kernel.
-/
theorem canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_nextPair_given_environment_prefix
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : Thompson.HistoryAlgorithm Action Reward)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Reward)
    (n : Nat) :
    condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          sample.2 (n + 1))
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          (sample.1, Preorder.frestrictLe n sample.2))
        (prior ⊗ₘ
          Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
            algorithm environment) =ᵐ[
      (prior ⊗ₘ
          Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
            algorithm environment).map
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          (sample.1, Preorder.frestrictLe n sample.2))]
      Thompson.measurableEnvironmentHistoryStepKernel
        algorithm environment n := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd))
    ((measurable_pi_apply (n + 1)).comp measurable_snd)
  exact
    canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_prefix_next_eq_compProd
      prior algorithm environment n

/-- The sampled EXP3 distribution viewed on a retained environment/prefix history. -/
noncomputable def sampledEnvironmentHistoryDistributionSource
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (n : Nat) :
    MeasurableFiniteActionDistribution arms
      (fun input : Env × History.FinitePairHistory Action Real n =>
        sampledHistoryDistribution arms eta gamma n input.2) where
  distribution input :=
    (exploredHistoryDistributionSource arms harms eta gamma
      (sampledHistoryScore arms eta gamma)
      (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
      hgamma_nonneg hgamma_le_one n).distribution input.2
  measurable_prob action haction :=
    ((exploredHistoryDistributionSource arms harms eta gamma
      (sampledHistoryScore arms eta gamma)
      (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
      hgamma_nonneg hgamma_le_one n).measurable_prob action haction).comp
        measurable_snd

/--
Predictable successor losses satisfy the regularity contract required by the
EXP3 conditional first- and second-moment transport layer.
-/
theorem sampledPredictableSuccessorLossRegularity
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    BoundedMeasurableLossWithProbabilityFloor arms
      (fun input : Env × History.FinitePairHistory Action Real n =>
        sampledHistoryDistribution arms eta gamma n input.2)
      (fun input : Env × History.FinitePairHistory Action Real n =>
        loss.successor n input.1 input.2)
      (gamma / (arms.card : Real)) where
  epsilon_pos := explorationFloor_pos arms harms gamma hgamma_pos
  prob_floor input action _haction :=
    sampledHistoryDistribution_floor arms harms eta gamma hgamma_le_one n
      input.2 action
  measurable_loss action _haction :=
    (loss.measurable_successor n).comp
      (measurable_fst.prodMk (measurable_snd.prodMk
        (measurable_const : Measurable
          (fun _ : Env × History.FinitePairHistory Action Real n => action))))
  loss_mem_Icc input action _haction :=
    loss.successor_mem_unitInterval n input.1 input.2 action

/-- The time-zero sampled EXP3 distribution viewed as a constant kernel on environments. -/
noncomputable def sampledInitialEnvironmentDistributionSource
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1) :
    MeasurableFiniteActionDistribution arms
      (fun _env : Env => initialExploredDistribution arms eta gamma) where
  distribution _env :=
    finiteActionDistribution_initialExploredDistribution arms harms eta gamma
      hgamma_nonneg hgamma_le_one
  measurable_prob _action _haction := measurable_const

/-- Initial predictable losses satisfy the sampled EXP3 regularity contract. -/
theorem sampledPredictableInitialLossRegularity
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    BoundedMeasurableLossWithProbabilityFloor arms
      (fun _env : Env => initialExploredDistribution arms eta gamma)
      loss.initial (gamma / (arms.card : Real)) where
  epsilon_pos := explorationFloor_pos arms harms gamma hgamma_pos
  prob_floor env action _haction := by
    simpa [initialExploredDistribution] using
      (exploredHistoryDistribution_floor arms harms eta gamma
        (fun _ : Unit => fun _ => 0) hgamma_le_one () action)
  measurable_loss action _haction :=
    loss.measurable_initial.comp
      (measurable_id.prodMk
        (measurable_const : Measurable (fun _ : Env => action)))
  loss_mem_Icc env action _haction :=
    loss.initial_mem_unitInterval env action

/-- Mixing the canonical trajectory through a prior preserves its global initial-pair law. -/
theorem canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_eval_zero
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : Thompson.HistoryAlgorithm Action Reward)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Reward) :
    (prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm environment).map
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          (sample.1, sample.2 0)) =
      prior ⊗ₘ
        Thompson.measurableEnvironmentInitialPairKernel algorithm environment := by
  let evalZero := fun trajectory : (k : Nat) -> Action × Reward => trajectory 0
  have hevalZero : Measurable evalZero := measurable_pi_apply 0
  calc
    _ = (prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm environment).map (Prod.map id evalZero) := by
      apply Measure.map_congr
      filter_upwards [] with sample
      rfl
    _ = prior ⊗ₘ
        (Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm environment).map evalZero :=
      (Measure.compProd_map hevalZero).symm
    _ = _ := by
      rw [Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero]

/-- The prior-mixed canonical trajectory retains the environment beside its initial action law. -/
theorem canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_action_zero
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : Thompson.HistoryAlgorithm Action Reward)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Reward) :
    (prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm environment).map
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          (sample.1, (sample.2 0).1)) =
      prior ⊗ₘ Kernel.const Env algorithm.initialAction := by
  let mu := prior ⊗ₘ
    Thompson.canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  let environmentInitialPair :=
    fun sample : Env × ((k : Nat) -> Action × Reward) =>
      (sample.1, sample.2 0)
  have hpair : Measurable environmentInitialPair :=
    measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
  calc
    _ = (mu.map environmentInitialPair).map (Prod.map id Prod.fst) := by
      rw [Measure.map_map (by fun_prop) hpair]
      apply Measure.map_congr
      filter_upwards [] with sample
      rfl
    _ = (prior ⊗ₘ
        Thompson.measurableEnvironmentInitialPairKernel
          algorithm environment).map (Prod.map id Prod.fst) := by
      rw [canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_eval_zero]
    _ = prior ⊗ₘ
        (Thompson.measurableEnvironmentInitialPairKernel
          algorithm environment).map Prod.fst :=
      (Measure.compProd_map measurable_fst).symm
    _ = _ := by
      congr 1
      rw [← Kernel.fst_eq,
        Thompson.measurableEnvironmentInitialPairKernel,
        Kernel.fst_compProd]

/-- Conditional on the retained environment, the canonical initial action follows `initialAction`. -/
theorem canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : Thompson.HistoryAlgorithm Action Reward)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Reward) :
    condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Reward) =>
          (sample.2 0).1)
        (fun sample : Env × ((k : Nat) -> Action × Reward) => sample.1)
        (prior ⊗ₘ
          Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
            algorithm environment) =ᵐ[
      (prior ⊗ₘ
          Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
            algorithm environment).map
        (fun sample : Env × ((k : Nat) -> Action × Reward) => sample.1)]
      Kernel.const Env algorithm.initialAction := by
  let history :=
    fun sample : Env × ((k : Nat) -> Action × Reward) => sample.1
  let action :=
    fun sample : Env × ((k : Nat) -> Action × Reward) => (sample.2 0).1
  have hhistory : Measurable history := by fun_prop
  have haction : Measurable action := by fun_prop
  change condDistrib action history
      (prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm environment) =ᵐ[
    (prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm environment).map history]
    Kernel.const Env algorithm.initialAction
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hhistory haction
  have hhistory :
      (prior ⊗ₘ
          Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
            algorithm environment).map
          (fun sample : Env × ((k : Nat) -> Action × Reward) => sample.1) =
        prior := by
    change (prior ⊗ₘ
      Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
        algorithm environment).fst = prior
    exact Measure.fst_compProd prior
      (Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
        algorithm environment)
  rw [hhistory]
  exact
    canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_action_zero
      prior algorithm environment

/--
Under predictable deterministic feedback, the observed initial reward is the
initial loss-vector coordinate selected by the initial action.
-/
theorem canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [Nonempty Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : Thompson.HistoryAlgorithm Action Real)
    (loss : PredictableLossVector Env Action) :
    (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 0).2) =ᵐ[
      prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm loss.environment]
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        loss.initial sample.1 (sample.2 0).1) := by
  let trajectoryKernel :=
    Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
      algorithm loss.environment
  let mu := prior ⊗ₘ trajectoryKernel
  let joinEnvironmentInitial :=
    fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, sample.2 0)
  have hinitial : Measurable
      (fun sample : Env × (Action × Real) =>
        loss.initial sample.1 sample.2.1) :=
    loss.measurable_initial.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hp : MeasurableSet
      {sample : Env × (Action × Real) |
        sample.2.2 = loss.initial sample.1 sample.2.1} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) hinitial
  have hkernel :
      mu.map joinEnvironmentInitial =
        prior ⊗ₘ
          Thompson.measurableEnvironmentInitialPairKernel
            algorithm loss.environment := by
    simpa [mu, trajectoryKernel, joinEnvironmentInitial] using
      (canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_eval_zero
        prior algorithm loss.environment)
  have hjoint : ∀ᵐ sample ∂
      prior ⊗ₘ
        Thompson.measurableEnvironmentInitialPairKernel
          algorithm loss.environment,
      sample.2.2 = loss.initial sample.1 sample.2.1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with env
    have hpPair : MeasurableSet
        {pair : Action × Real | pair.2 = loss.initial env pair.1} :=
      measurableSet_eq_fun measurable_snd
        (loss.measurable_initial.comp
          (measurable_const.prodMk measurable_fst))
    rw [Thompson.measurableEnvironmentInitialPairKernel_apply]
    apply Measure.ae_compProd_of_ae_ae hpPair
    filter_upwards [] with action
    rw [Thompson.MeasurableHistoryEnvironment.at, Kernel.comap_apply,
      PredictableLossVector.environment_initialFeedback_apply]
    simp
  rw [← hkernel] at hjoint
  have hsource :=
    (ae_map_iff
      (measurable_fst.prodMk
        ((measurable_pi_apply 0).comp measurable_snd)).aemeasurable hp).mp hjoint
  simpa [mu, trajectoryKernel, joinEnvironmentInitial] using hsource

/--
The time-zero sampled EXP3 estimator has the observed-scalar armwise first
moment and exact probability-mixed estimator-square moment.
-/
theorem sampledPredictableObservedInitial_first_second_moment
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let prob := initialExploredDistribution arms eta gamma
    (integral mu (fun sample =>
        importanceWeightedLoss prob (fun _ => (sample.2 0).2)
          (sample.2 0).1 comparator) =
      integral prior (fun env => loss.initial env comparator)) ∧
    (integral mu (fun sample =>
        mixedSquaredImportanceWeightedLoss arms prob
          (fun _ => (sample.2 0).2) (sample.2 0).1) =
      integral prior (fun env =>
        arms.sum (fun action => (loss.initial env action) ^ 2))) := by
  dsimp only
  let algorithm := sampledImportanceWeightedHistoryAlgorithm arms harms
    eta gamma hgamma_pos.le hgamma_le_one
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let prob := fun _env : Env => initialExploredDistribution arms eta gamma
  let roundLoss := loss.initial
  let source := sampledInitialEnvironmentDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
  let policy := finiteActionKernel arms prob source
  let epsilon := gamma / (arms.card : Real)
  have hhistory : Measurable history := by fun_prop
  have haction : Measurable action := by fun_prop
  have hregularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob roundLoss epsilon := by
    simpa [prob, roundLoss, epsilon] using
      (sampledPredictableInitialLossRegularity arms harms eta gamma
        hgamma_pos hgamma_le_one loss)
  have hkernel : Kernel.const Env algorithm.initialAction = policy := by
    ext env event hevent
    rw [Kernel.const_apply, finiteActionKernel_apply]
    rfl
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    have hbase :=
      canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
        prior algorithm loss.environment
    rw [hkernel] at hbase
    simpa [mu, algorithm, history, action,
      sampledImportanceWeightedTrajectoryKernel] using hbase
  have hpolicy : policy =ᵐ[mu.map history]
      fun env => finiteActionMeasure arms (prob env) := by
    filter_upwards [] with env
    rw [finiteActionKernel_apply]
  have hhistoryMarginal : mu.map history = prior := by
    change (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment).fst = prior
    exact Measure.fst_compProd prior
      (sampledImportanceWeightedTrajectoryKernel arms harms eta gamma
        hgamma_pos.le hgamma_le_one loss.environment)
  have hscoreFirst : Measurable (fun z : Env × Action =>
      importanceWeightedLoss (prob z.1) (roundLoss z.1)
        z.2 comparator) :=
    measurable_importanceWeightedLoss_score arms prob roundLoss source epsilon
      hregularity comparator hcomparator
  have hintegrableFirst : Integrable (fun z : Env × Action =>
      importanceWeightedLoss (prob z.1) (roundLoss z.1)
        z.2 comparator) (mu.map history ⊗ₘ policy) := by
    rw [hhistoryMarginal]
    exact integrable_importanceWeightedLoss_score prior arms prob roundLoss
      source epsilon hregularity comparator hcomparator
  have hscoreSecond : Measurable (fun z : Env × Action =>
      mixedSquaredImportanceWeightedLoss arms (prob z.1)
        (roundLoss z.1) z.2) :=
    measurable_mixedSquaredImportanceWeightedLoss_score
      arms prob roundLoss source epsilon hregularity
  have hintegrableSecond : Integrable (fun z : Env × Action =>
      mixedSquaredImportanceWeightedLoss arms (prob z.1)
        (roundLoss z.1) z.2) (mu.map history ⊗ₘ policy) := by
    rw [hhistoryMarginal]
    exact integrable_mixedSquaredImportanceWeightedLoss_score
      prior arms prob roundLoss source epsilon hregularity
  have hvectorFirst :
      integral mu (fun sample =>
          importanceWeightedLoss (prob (history sample))
            (roundLoss (history sample)) (action sample) comparator) =
        integral prior (fun env => roundLoss env comparator) := by
    have hresult :=
      integral_importanceWeightedLoss_eq_integral_loss_of_condDistrib
        mu history hhistory action haction arms prob roundLoss
        source.distribution (fun env candidate hcandidate =>
          hregularity.prob_pos env candidate hcandidate)
        policy hpolicy hcond comparator hcomparator hscoreFirst hintegrableFirst
    rw [hhistoryMarginal] at hresult
    exact hresult
  have hvectorSecond :
      integral mu (fun sample =>
          mixedSquaredImportanceWeightedLoss arms (prob (history sample))
            (roundLoss (history sample)) (action sample)) =
        integral prior (fun env =>
          arms.sum (fun candidate => (roundLoss env candidate) ^ 2)) := by
    have hresult :=
      integral_mixedSquaredImportanceWeightedLoss_eq_integral_sum_loss_sq_of_condDistrib
        mu history hhistory action haction arms prob roundLoss
        source.distribution (fun env candidate hcandidate =>
          hregularity.prob_pos env candidate hcandidate)
        policy hpolicy hcond hscoreSecond hintegrableSecond
    rw [hhistoryMarginal] at hresult
    exact hresult
  have hreward :
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 0).2) =ᵐ[mu]
        (fun sample => loss.initial sample.1 (sample.2 0).1) := by
    simpa [mu, algorithm, sampledImportanceWeightedTrajectoryKernel] using
      (canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
        prior algorithm loss)
  constructor
  · calc
      integral mu (fun sample =>
          importanceWeightedLoss (initialExploredDistribution arms eta gamma)
            (fun _ => (sample.2 0).2) (sample.2 0).1 comparator) =
          integral mu (fun sample =>
            importanceWeightedLoss (prob (history sample))
              (roundLoss (history sample)) (action sample) comparator) := by
        apply integral_congr_ae
        filter_upwards [hreward] with sample hsample
        by_cases hchosen : (sample.2 0).1 = comparator
        · simp [importanceWeightedLoss, hchosen, hsample,
            history, action, prob, roundLoss]
        · simp [importanceWeightedLoss, hchosen, action]
      _ = integral prior (fun env => loss.initial env comparator) := by
        simpa [roundLoss] using hvectorFirst
  · calc
      integral mu (fun sample =>
          mixedSquaredImportanceWeightedLoss arms
            (initialExploredDistribution arms eta gamma)
            (fun _ => (sample.2 0).2) (sample.2 0).1) =
          integral mu (fun sample =>
            mixedSquaredImportanceWeightedLoss arms (prob (history sample))
              (roundLoss (history sample)) (action sample)) := by
        apply integral_congr_ae
        filter_upwards [hreward] with sample hsample
        unfold mixedSquaredImportanceWeightedLoss
        apply Finset.sum_congr rfl
        intro candidate _hcandidate
        by_cases hchosen : (sample.2 0).1 = candidate
        · simp [importanceWeightedLoss, hchosen, hsample,
            history, action, prob, roundLoss]
        · simp [importanceWeightedLoss, hchosen, action]
      _ = integral prior (fun env =>
          arms.sum (fun candidate => (loss.initial env candidate) ^ 2)) := by
        simpa [roundLoss] using hvectorSecond

/--
Under predictable deterministic feedback, the observed successor reward is the
loss-vector coordinate selected by the action in the same successor pair.
-/
theorem canonicalPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : Thompson.HistoryAlgorithm Action Real)
    (loss : PredictableLossVector Env Action)
    (n : Nat) :
    (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 (n + 1)).2) =ᵐ[
      prior ⊗ₘ
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
          algorithm loss.environment]
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        loss.successor n sample.1 (Preorder.frestrictLe n sample.2)
          (sample.2 (n + 1)).1) := by
  let trajectoryKernel :=
    Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
      algorithm loss.environment
  let mu := prior ⊗ₘ trajectoryKernel
  let joinEnvironmentPrefixNext :=
    fun sample : Env × ((k : Nat) -> Action × Real) =>
      ((sample.1, Preorder.frestrictLe n sample.2), sample.2 (n + 1))
  have hsuccessor : Measurable
      (fun sample : (Env × History.FinitePairHistory Action Real n) ×
          (Action × Real) =>
        loss.successor n sample.1.1 sample.1.2 sample.2.1) :=
    (loss.measurable_successor n).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd)))
  have hp : MeasurableSet
      {sample : (Env × History.FinitePairHistory Action Real n) ×
          (Action × Real) |
        sample.2.2 =
          loss.successor n sample.1.1 sample.1.2 sample.2.1} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) hsuccessor
  have hkernel :
      mu.map joinEnvironmentPrefixNext =
        mu.map (fun sample =>
          (sample.1, Preorder.frestrictLe n sample.2)) ⊗ₘ
            Thompson.measurableEnvironmentHistoryStepKernel
              algorithm loss.environment n := by
    simpa [mu, trajectoryKernel, joinEnvironmentPrefixNext] using
      (canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_prefix_next_eq_compProd
        prior algorithm loss.environment n)
  have hjoint : ∀ᵐ sample ∂
      mu.map (fun sample =>
          (sample.1, Preorder.frestrictLe n sample.2)) ⊗ₘ
        Thompson.measurableEnvironmentHistoryStepKernel
          algorithm loss.environment n,
      sample.2.2 =
        loss.successor n sample.1.1 sample.1.2 sample.2.1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with environmentHistory
    have hpPair : MeasurableSet
        {pair : Action × Real |
          pair.2 = loss.successor n environmentHistory.1
            environmentHistory.2 pair.1} :=
      measurableSet_eq_fun measurable_snd
        ((loss.measurable_successor n).comp
          (measurable_const.prodMk
            (measurable_const.prodMk measurable_fst)))
    rw [Thompson.measurableEnvironmentHistoryStepKernel,
      Kernel.compProd_apply_eq_compProd_sectR]
    apply Measure.ae_compProd_of_ae_ae hpPair
    filter_upwards [] with action
    rw [Kernel.sectR_apply, Kernel.comap_apply,
      PredictableLossVector.environment_feedback_apply]
    simp
  rw [← hkernel] at hjoint
  have hsource :=
    (ae_map_iff
      ((measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).prodMk
          ((measurable_pi_apply (n + 1)).comp measurable_snd)).aemeasurable
      hp).mp hjoint
  simpa [mu, trajectoryKernel, joinEnvironmentPrefixNext] using hsource

/--
Concrete sampled-loss EXP3 observes exactly the selected predictable successor
loss in every round, almost surely under the environment/trajectory mixture.
-/
theorem sampledPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 (n + 1)).2) =ᵐ[
      prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        eta gamma hgamma_nonneg hgamma_le_one loss.environment]
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        loss.successor n sample.1 (Preorder.frestrictLe n sample.2)
          (sample.2 (n + 1)).1) := by
  simpa [sampledImportanceWeightedTrajectoryKernel] using
    (canonicalPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
      prior
      (sampledImportanceWeightedHistoryAlgorithm arms harms eta gamma
        hgamma_nonneg hgamma_le_one)
      loss n)

/--
The concrete sampled EXP3 successor round has the armwise unbiased first moment
and the exact probability-mixed estimator-square moment for every predictable
loss vector with positive exploration.
-/
theorem sampledPredictableSuccessorLoss_first_second_moment
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    let prob := fun input : Env × History.FinitePairHistory Action Real n =>
      sampledHistoryDistribution arms eta gamma n input.2
    let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
      loss.successor n input.1 input.2
    (integral mu (fun sample =>
        importanceWeightedLoss (prob (history sample))
          (roundLoss (history sample)) (sample.2 (n + 1)).1 comparator) =
      integral (mu.map history) (fun input => roundLoss input comparator)) ∧
    (integral mu (fun sample =>
        mixedSquaredImportanceWeightedLoss arms (prob (history sample))
          (roundLoss (history sample)) (sample.2 (n + 1)).1) =
      integral (mu.map history) (fun input =>
        arms.sum (fun action => (roundLoss input action) ^ 2))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 (n + 1)).1
  let prob := fun input : Env × History.FinitePairHistory Action Real n =>
    sampledHistoryDistribution arms eta gamma n input.2
  let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
    loss.successor n input.1 input.2
  let localSource :=
    exploredHistoryDistributionSource arms harms eta gamma
      (sampledHistoryScore arms eta gamma)
      (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
      hgamma_pos.le hgamma_le_one n
  let source := sampledEnvironmentHistoryDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
  let policy : Kernel
      (Env × History.FinitePairHistory Action Real n) Action :=
    (finiteActionKernel arms
      (sampledHistoryDistribution arms eta gamma n) localSource).comap
        (fun input : Env × History.FinitePairHistory Action Real n => input.2)
        (measurable_snd : Measurable
          (fun input : Env × History.FinitePairHistory Action Real n =>
            input.2))
  let epsilon := gamma / (arms.card : Real)
  have hhistory : Measurable history :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action := by
    change Measurable
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 (n + 1)).1)
    fun_prop
  have hregularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob roundLoss epsilon := by
    simpa [prob, roundLoss, epsilon] using
      (sampledPredictableSuccessorLossRegularity arms harms eta gamma
        hgamma_pos hgamma_le_one loss n)
  have hpolicyEq :
      policy = finiteActionKernel arms prob source := by
    ext input event hevent
    rw [Kernel.comap_apply, finiteActionKernel_apply,
      finiteActionKernel_apply]
  have hpolicy : policy =ᵐ[mu.map history]
      fun input => finiteActionMeasure arms (prob input) := by
    filter_upwards [] with input
    rw [hpolicyEq, finiteActionKernel_apply]
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    simpa [mu, history, action, policy, localSource] using
      (sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss n)
  have hscoreFirst : Measurable
      (fun z : (Env × History.FinitePairHistory Action Real n) × Action =>
        importanceWeightedLoss (prob z.1) (roundLoss z.1)
          z.2 comparator) :=
    measurable_importanceWeightedLoss_score arms prob roundLoss source epsilon
      hregularity comparator hcomparator
  have hintegrableFirst : Integrable
      (fun z : (Env × History.FinitePairHistory Action Real n) × Action =>
        importanceWeightedLoss (prob z.1) (roundLoss z.1)
          z.2 comparator)
      (mu.map history ⊗ₘ policy) := by
    rw [hpolicyEq]
    exact integrable_importanceWeightedLoss_score (mu.map history)
      arms prob roundLoss source epsilon hregularity comparator hcomparator
  have hscoreSecond : Measurable
      (fun z : (Env × History.FinitePairHistory Action Real n) × Action =>
        mixedSquaredImportanceWeightedLoss arms (prob z.1)
          (roundLoss z.1) z.2) :=
    measurable_mixedSquaredImportanceWeightedLoss_score
      arms prob roundLoss source epsilon hregularity
  have hintegrableSecond : Integrable
      (fun z : (Env × History.FinitePairHistory Action Real n) × Action =>
        mixedSquaredImportanceWeightedLoss arms (prob z.1)
          (roundLoss z.1) z.2)
      (mu.map history ⊗ₘ policy) := by
    rw [hpolicyEq]
    exact integrable_mixedSquaredImportanceWeightedLoss_score
      (mu.map history) arms prob roundLoss source epsilon hregularity
  constructor
  · exact integral_importanceWeightedLoss_eq_integral_loss_of_condDistrib
      mu history hhistory action haction arms prob roundLoss
      source.distribution (fun input candidate hcandidate =>
        hregularity.prob_pos input candidate hcandidate)
      policy hpolicy hcond comparator hcomparator hscoreFirst hintegrableFirst
  · exact
      integral_mixedSquaredImportanceWeightedLoss_eq_integral_sum_loss_sq_of_condDistrib
        mu history hhistory action haction arms prob roundLoss
        source.distribution (fun input candidate hcandidate =>
          hregularity.prob_pos input candidate hcandidate)
        policy hpolicy hcond hscoreSecond hintegrableSecond

/--
Observed-scalar form of the sampled EXP3 roundwise moment theorem.  The score
uses only the reward coordinate stored in the generated trajectory; the right
sides expose the full predictable loss vector required by regret analysis.
-/
theorem sampledPredictableObservedSuccessor_first_second_moment
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    let prob := fun input : Env × History.FinitePairHistory Action Real n =>
      sampledHistoryDistribution arms eta gamma n input.2
    let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
      loss.successor n input.1 input.2
    (integral mu (fun sample =>
        importanceWeightedLoss (prob (history sample))
          (fun _ => (sample.2 (n + 1)).2)
          (sample.2 (n + 1)).1 comparator) =
      integral (mu.map history) (fun input => roundLoss input comparator)) ∧
    (integral mu (fun sample =>
        mixedSquaredImportanceWeightedLoss arms (prob (history sample))
          (fun _ => (sample.2 (n + 1)).2)
          (sample.2 (n + 1)).1) =
      integral (mu.map history) (fun input =>
        arms.sum (fun action => (roundLoss input action) ^ 2))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  let prob := fun input : Env × History.FinitePairHistory Action Real n =>
    sampledHistoryDistribution arms eta gamma n input.2
  let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
    loss.successor n input.1 input.2
  have hcore := sampledPredictableSuccessorLoss_first_second_moment
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
      comparator hcomparator
  dsimp only at hcore
  have hreward :
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 (n + 1)).2) =ᵐ[mu]
        (fun sample =>
          loss.successor n sample.1 (Preorder.frestrictLe n sample.2)
            (sample.2 (n + 1)).1) := by
    simpa [mu] using
      (sampledPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
        prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss n)
  constructor
  · calc
      integral mu (fun sample =>
          importanceWeightedLoss (prob (history sample))
            (fun _ => (sample.2 (n + 1)).2)
            (sample.2 (n + 1)).1 comparator) =
          integral mu (fun sample =>
            importanceWeightedLoss (prob (history sample))
              (roundLoss (history sample))
              (sample.2 (n + 1)).1 comparator) := by
        apply integral_congr_ae
        filter_upwards [hreward] with sample hsample
        by_cases hchosen : (sample.2 (n + 1)).1 = comparator
        · simp [importanceWeightedLoss, hchosen, hsample,
            history, roundLoss]
        · simp [importanceWeightedLoss, hchosen]
      _ = integral (mu.map history)
          (fun input => roundLoss input comparator) := by
        simpa [mu, history, prob, roundLoss] using hcore.1
  · calc
      integral mu (fun sample =>
          mixedSquaredImportanceWeightedLoss arms (prob (history sample))
            (fun _ => (sample.2 (n + 1)).2)
            (sample.2 (n + 1)).1) =
          integral mu (fun sample =>
            mixedSquaredImportanceWeightedLoss arms (prob (history sample))
              (roundLoss (history sample))
              (sample.2 (n + 1)).1) := by
        apply integral_congr_ae
        filter_upwards [hreward] with sample hsample
        unfold mixedSquaredImportanceWeightedLoss
        apply Finset.sum_congr rfl
        intro candidate _hcandidate
        by_cases hchosen : (sample.2 (n + 1)).1 = candidate
        · simp [importanceWeightedLoss, hchosen, hsample,
            history, roundLoss]
        · simp [importanceWeightedLoss, hchosen]
      _ = integral (mu.map history) (fun input =>
          arms.sum (fun action => (roundLoss input action) ^ 2)) := by
        simpa [mu, history, prob, roundLoss] using hcore.2

/-- Sampling probabilities used by the concrete trajectory at every actual time index. -/
noncomputable def sampledTrajectoryProbabilityAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Action -> Real :=
  match t with
  | 0 => initialExploredDistribution arms eta gamma
  | n + 1 => sampledHistoryDistribution arms eta gamma n
      (Preorder.frestrictLe n sample.2)

/-- Predictable loss vector selected before the action at every actual time index. -/
def predictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Action -> Real :=
  match t with
  | 0 => loss.initial sample.1
  | n + 1 => loss.successor n sample.1
      (Preorder.frestrictLe n sample.2)

/-- The scalar-feedback importance-weighted coordinate used at an actual time. -/
noncomputable def observedImportanceWeightedLossAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    (comparator : Action) : Real :=
  importanceWeightedLoss (sampledTrajectoryProbabilityAt arms eta gamma t sample)
    (fun _ => (sample.2 t).2) (sample.2 t).1 comparator

/-- The scalar-feedback probability-mixed estimator square used at an actual time. -/
noncomputable def observedMixedSquaredImportanceWeightedLossAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  mixedSquaredImportanceWeightedLoss arms
    (sampledTrajectoryProbabilityAt arms eta gamma t sample)
    (fun _ => (sample.2 t).2) (sample.2 t).1

/-- Measurable finite-action source for the sampled probability vector at any time. -/
noncomputable def sampledTrajectoryProbabilitySourceAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (t : Nat) :
    MeasurableFiniteActionDistribution arms
      (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t) := by
  cases t with
  | zero =>
      exact
        { distribution := fun _sample =>
            finiteActionDistribution_initialExploredDistribution
              arms harms eta gamma hgamma_nonneg hgamma_le_one
          measurable_prob := fun _action _haction => measurable_const }
  | succ n =>
      let source := exploredHistoryDistributionSource arms harms eta gamma
        (sampledHistoryScore arms eta gamma)
        (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
        hgamma_nonneg hgamma_le_one n
      exact
        { distribution := fun sample =>
            source.distribution (Preorder.frestrictLe n sample.2)
          measurable_prob := fun action haction =>
            (source.measurable_prob action haction).comp
              ((Preorder.measurable_frestrictLe n).comp measurable_snd) }

/-- Predictable trajectory losses satisfy one uniform regularity interface at every time. -/
theorem sampledPredictableTrajectoryLossRegularityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    BoundedMeasurableLossWithProbabilityFloor arms
      (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
      (predictableLossAt loss t) (gamma / (arms.card : Real)) := by
  cases t with
  | zero =>
      refine
        { epsilon_pos := explorationFloor_pos arms harms gamma hgamma_pos
          prob_floor := ?_
          measurable_loss := ?_
          loss_mem_Icc := ?_ }
      · intro sample action _haction
        simpa [sampledTrajectoryProbabilityAt, initialExploredDistribution] using
          (exploredHistoryDistribution_floor arms harms eta gamma
            (fun _ : Unit => fun _ => 0) hgamma_le_one () action)
      · intro action _haction
        exact loss.measurable_initial.comp
          (measurable_fst.prodMk
            (measurable_const : Measurable
              (fun _ : Env × ((k : Nat) -> Action × Real) => action)))
      · intro sample action _haction
        exact loss.initial_mem_unitInterval sample.1 action
  | succ n =>
      refine
        { epsilon_pos := explorationFloor_pos arms harms gamma hgamma_pos
          prob_floor := ?_
          measurable_loss := ?_
          loss_mem_Icc := ?_ }
      · intro sample action _haction
        simpa [sampledTrajectoryProbabilityAt] using
          (sampledHistoryDistribution_floor arms harms eta gamma
            hgamma_le_one n (Preorder.frestrictLe n sample.2) action)
      · intro action _haction
        exact (loss.measurable_successor n).comp
          (measurable_fst.prodMk
            (((Preorder.measurable_frestrictLe n).comp measurable_snd).prodMk
              (measurable_const : Measurable
                (fun _ : Env × ((k : Nat) -> Action × Real) => action))))
      · intro sample action _haction
        exact loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) action

theorem measurable_predictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : PredictableLossVector Env Action) (t : Nat)
    (action : Action) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Real) =>
      predictableLossAt loss t sample action) := by
  cases t with
  | zero =>
      exact loss.measurable_initial.comp
        (measurable_fst.prodMk measurable_const)
  | succ n =>
      exact (loss.measurable_successor n).comp
        (measurable_fst.prodMk
          (((Preorder.measurable_frestrictLe n).comp measurable_snd).prodMk
            (measurable_const : Measurable
              (fun _ : Env × ((k : Nat) → Action × Real) => action))))

theorem measurable_observedImportanceWeightedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (t : Nat) (comparator : Action) (hcomparator : comparator ∈ arms) :
    Measurable (observedImportanceWeightedLossAt
      (Env := Env) arms eta gamma t · comparator) := by
  apply measurable_observedImportanceWeightedLoss
  · exact (sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms
      eta gamma hgamma_nonneg hgamma_le_one t).measurable_prob
        comparator hcomparator
  · fun_prop
  · fun_prop

theorem measurable_observedMixedSquaredImportanceWeightedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (t : Nat) :
    Measurable (observedMixedSquaredImportanceWeightedLossAt
      (Env := Env) arms eta gamma t) := by
  unfold observedMixedSquaredImportanceWeightedLossAt
  unfold mixedSquaredImportanceWeightedLoss
  refine Finset.measurable_sum arms fun action haction => ?_
  exact
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_nonneg hgamma_le_one t).measurable_prob action haction).mul
      ((measurable_observedImportanceWeightedLossAt (Env := Env) arms harms
        eta gamma hgamma_nonneg hgamma_le_one t action haction).pow_const 2)

theorem integrable_predictableImportanceWeightedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let prob := sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t
    let roundLoss := predictableLossAt loss t
    Integrable (fun sample => importanceWeightedLoss (prob sample)
      (roundLoss sample) (sample.2 t).1 comparator) mu := by
  dsimp only
  let source : MeasurableFiniteActionDistribution arms
      (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t) :=
    sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms
    eta gamma hgamma_pos.le hgamma_le_one t
  let regularity : BoundedMeasurableLossWithProbabilityFloor arms
      (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
      (predictableLossAt loss t) (gamma / (arms.card : Real)) :=
    sampledPredictableTrajectoryLossRegularityAt arms harms eta gamma
      hgamma_pos hgamma_le_one loss t
  have hchosen : Measurable
      (fun sample : Env × ((k : Nat) → Action × Real) => (sample.2 t).1) := by
    fun_prop
  exact integrable_importanceWeightedLoss_selected_of_isFiniteMeasure mu arms
      (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
      (predictableLossAt loss t) source (gamma / (arms.card : Real)) regularity
      (fun sample => (sample.2 t).1) hchosen comparator hcomparator

theorem integrable_predictableMixedSquaredImportanceWeightedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    let prob := sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t
    let roundLoss := predictableLossAt loss t
    Integrable (fun sample => mixedSquaredImportanceWeightedLoss arms
      (prob sample) (roundLoss sample) (sample.2 t).1) mu := by
  dsimp only
  let source : MeasurableFiniteActionDistribution arms
      (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t) :=
    sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms
    eta gamma hgamma_pos.le hgamma_le_one t
  let regularity : BoundedMeasurableLossWithProbabilityFloor arms
      (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
      (predictableLossAt loss t) (gamma / (arms.card : Real)) :=
    sampledPredictableTrajectoryLossRegularityAt arms harms eta gamma
      hgamma_pos hgamma_le_one loss t
  have hchosen : Measurable
      (fun sample : Env × ((k : Nat) → Action × Real) => (sample.2 t).1) := by
    fun_prop
  exact integrable_mixedSquaredImportanceWeightedLoss_selected_of_isFiniteMeasure
      mu arms (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
      (predictableLossAt loss t) source (gamma / (arms.card : Real)) regularity
      (fun sample => (sample.2 t).1) hchosen

theorem integrable_predictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real))) [IsFiniteMeasure mu]
    (loss : PredictableLossVector Env Action) (t : Nat) (action : Action) :
    Integrable (fun sample => predictableLossAt loss t sample action) mu := by
  refine Integrable.of_bound
    (measurable_predictableLossAt loss t action).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun sample => by
    cases t with
    | zero =>
        have hloss := loss.initial_mem_unitInterval sample.1 action
        simpa [predictableLossAt, Real.norm_eq_abs, abs_of_nonneg hloss.1]
          using hloss.2
    | succ n =>
        have hloss := loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) action
        simpa [predictableLossAt, Real.norm_eq_abs, abs_of_nonneg hloss.1]
          using hloss.2

theorem integrable_predictableLossSqSumAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (loss : PredictableLossVector Env Action) (t : Nat) :
    Integrable (fun sample =>
      arms.sum (fun action => (predictableLossAt loss t sample action) ^ 2)) mu := by
  apply IntegrabilitySums.integrable_finset_sum mu arms
  intro action _haction
  refine Integrable.of_bound
    ((measurable_predictableLossAt loss t action).pow_const 2).aestronglyMeasurable
    1 ?_
  exact Filter.Eventually.of_forall fun sample => by
    cases t with
    | zero =>
        have hloss := loss.initial_mem_unitInterval sample.1 action
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa [predictableLossAt] using
          (sq_le_sq₀ hloss.1 zero_le_one).2 hloss.2
    | succ n =>
        have hloss := loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) action
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa [predictableLossAt] using
          (sq_le_sq₀ hloss.1 zero_le_one).2 hloss.2

/-- On the generated predictable trajectory, observed scalar scores agree
almost everywhere with their latent predictable-loss counterparts. -/
theorem observedAt_eq_predictableAt_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (comparator : Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ((fun sample => observedImportanceWeightedLossAt
        arms eta gamma t sample comparator) =ᵐ[mu]
      (fun sample => importanceWeightedLoss
        (sampledTrajectoryProbabilityAt arms eta gamma t sample)
        (predictableLossAt loss t sample) (sample.2 t).1 comparator)) ∧
    ((fun sample => observedMixedSquaredImportanceWeightedLossAt
        arms eta gamma t sample) =ᵐ[mu]
      (fun sample => mixedSquaredImportanceWeightedLoss arms
        (sampledTrajectoryProbabilityAt arms eta gamma t sample)
        (predictableLossAt loss t sample) (sample.2 t).1)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  cases t with
  | zero =>
      have hreward :
          (fun sample : Env × ((k : Nat) → Action × Real) =>
            (sample.2 0).2) =ᵐ[mu]
          (fun sample => loss.initial sample.1 (sample.2 0).1) := by
        simpa [mu, sampledImportanceWeightedTrajectoryKernel] using
          (canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
            prior (sampledImportanceWeightedHistoryAlgorithm arms harms eta gamma
              hgamma_nonneg hgamma_le_one) loss)
      constructor
      · filter_upwards [hreward] with sample hsample
        by_cases hchosen : (sample.2 0).1 = comparator
        · simp [observedImportanceWeightedLossAt, sampledTrajectoryProbabilityAt,
            predictableLossAt, importanceWeightedLoss, hchosen, hsample]
        · simp [observedImportanceWeightedLossAt, importanceWeightedLoss, hchosen]
      · filter_upwards [hreward] with sample hsample
        unfold observedMixedSquaredImportanceWeightedLossAt
        unfold mixedSquaredImportanceWeightedLoss
        apply Finset.sum_congr rfl
        intro candidate _hcandidate
        by_cases hchosen : (sample.2 0).1 = candidate
        · simp [sampledTrajectoryProbabilityAt, predictableLossAt,
            importanceWeightedLoss, hchosen, hsample]
        · simp [sampledTrajectoryProbabilityAt, importanceWeightedLoss, hchosen]
  | succ n =>
      have hreward :
          (fun sample : Env × ((k : Nat) → Action × Real) =>
            (sample.2 (n + 1)).2) =ᵐ[mu]
          (fun sample => loss.successor n sample.1
            (Preorder.frestrictLe n sample.2) (sample.2 (n + 1)).1) := by
        simpa [mu] using
          (sampledPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
            prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)
      constructor
      · filter_upwards [hreward] with sample hsample
        by_cases hchosen : (sample.2 (n + 1)).1 = comparator
        · simp [observedImportanceWeightedLossAt, sampledTrajectoryProbabilityAt,
            predictableLossAt, importanceWeightedLoss, hchosen, hsample]
        · simp [observedImportanceWeightedLossAt, importanceWeightedLoss, hchosen]
      · filter_upwards [hreward] with sample hsample
        unfold observedMixedSquaredImportanceWeightedLossAt
        unfold mixedSquaredImportanceWeightedLoss
        apply Finset.sum_congr rfl
        intro candidate _hcandidate
        by_cases hchosen : (sample.2 (n + 1)).1 = candidate
        · simp [sampledTrajectoryProbabilityAt, predictableLossAt,
            importanceWeightedLoss, hchosen, hsample]
        · simp [sampledTrajectoryProbabilityAt, importanceWeightedLoss, hchosen]

/-- The two observed score families are integrable under the generated
predictable trajectory law at every actual time index. -/
theorem integrable_observedAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Integrable (fun sample => observedImportanceWeightedLossAt
      arms eta gamma t sample comparator) mu ∧
    Integrable (fun sample => observedMixedSquaredImportanceWeightedLossAt
      arms eta gamma t sample) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  have hlatentFirst := integrable_predictableImportanceWeightedLossAt
    mu arms harms eta gamma hgamma_pos hgamma_le_one loss t
      comparator hcomparator
  have hlatentSecond := integrable_predictableMixedSquaredImportanceWeightedLossAt
    mu arms harms eta gamma hgamma_pos hgamma_le_one loss t
  have hae := observedAt_eq_predictableAt_ae prior arms harms eta gamma
    hgamma_pos.le hgamma_le_one loss t comparator
  dsimp only at hae
  exact ⟨hlatentFirst.congr hae.1.symm, hlatentSecond.congr hae.2.symm⟩

/-- At every actual time, including time zero, the observed armwise first
moment and probability-mixed estimator-square moment equal the corresponding
predictable loss-vector moments on the common full trajectory law. -/
theorem sampledPredictableObservedAt_first_second_moment
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    (integral mu (fun sample => observedImportanceWeightedLossAt
        arms eta gamma t sample comparator) =
      integral mu (fun sample => predictableLossAt loss t sample comparator)) ∧
    (integral mu (fun sample => observedMixedSquaredImportanceWeightedLossAt
        arms eta gamma t sample) =
      integral mu (fun sample => arms.sum (fun action =>
        (predictableLossAt loss t sample action) ^ 2))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  cases t with
  | zero =>
      have hcore := sampledPredictableObservedInitial_first_second_moment
        prior arms harms eta gamma hgamma_pos hgamma_le_one loss
          comparator hcomparator
      dsimp only at hcore
      have hfst : mu.map (fun sample : Env × ((k : Nat) → Action × Real) =>
          sample.1) = prior := by
        change (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_le_one loss.environment).fst = prior
        exact Measure.fst_compProd prior
          (sampledImportanceWeightedTrajectoryKernel arms harms eta gamma
            hgamma_pos.le hgamma_le_one loss.environment)
      have hfirstMeas : Measurable
          (fun env : Env => loss.initial env comparator) :=
        loss.measurable_initial.comp
          (measurable_id.prodMk
            (measurable_const : Measurable (fun _ : Env => comparator)))
      have hfirstMap : integral mu (fun sample => loss.initial sample.1 comparator) =
          integral prior (fun env => loss.initial env comparator) := by
        calc
          integral mu (fun sample => loss.initial sample.1 comparator) =
              integral (mu.map (fun sample : Env × ((k : Nat) → Action × Real) =>
                sample.1)) (fun env => loss.initial env comparator) := by
            symm
            simpa only [Function.comp_apply] using
              (integral_map measurable_fst.aemeasurable
                hfirstMeas.aestronglyMeasurable)
          _ = integral prior (fun env => loss.initial env comparator) := by
            rw [hfst]
      have hsecondMeas : Measurable (fun env =>
          arms.sum (fun action => (loss.initial env action) ^ 2)) := by
        refine Finset.measurable_sum arms fun action _haction => ?_
        exact (loss.measurable_initial.comp
          (measurable_id.prodMk
            (measurable_const : Measurable (fun _ : Env => action)))).pow_const 2
      have hsecondMap : integral mu (fun sample =>
          arms.sum (fun action => (loss.initial sample.1 action) ^ 2)) =
          integral prior (fun env =>
            arms.sum (fun action => (loss.initial env action) ^ 2)) := by
        calc
          integral mu (fun sample =>
              arms.sum (fun action => (loss.initial sample.1 action) ^ 2)) =
              integral (mu.map (fun sample : Env × ((k : Nat) → Action × Real) =>
                sample.1)) (fun env =>
                  arms.sum (fun action => (loss.initial env action) ^ 2)) := by
            symm
            rw [integral_map measurable_fst.aemeasurable
              hsecondMeas.aestronglyMeasurable]
          _ = integral prior (fun env =>
              arms.sum (fun action => (loss.initial env action) ^ 2)) := by
            rw [hfst]
      constructor
      · calc
          integral mu (fun sample => observedImportanceWeightedLossAt
              arms eta gamma 0 sample comparator) =
              integral prior (fun env => loss.initial env comparator) := by
            simpa [mu, observedImportanceWeightedLossAt,
              sampledTrajectoryProbabilityAt] using hcore.1
          _ = integral mu (fun sample => predictableLossAt loss 0 sample comparator) := by
            simpa [predictableLossAt] using hfirstMap.symm
      · calc
          integral mu (fun sample => observedMixedSquaredImportanceWeightedLossAt
              arms eta gamma 0 sample) =
              integral prior (fun env =>
                arms.sum (fun action => (loss.initial env action) ^ 2)) := by
            simpa [mu, observedMixedSquaredImportanceWeightedLossAt,
              sampledTrajectoryProbabilityAt] using hcore.2
          _ = integral mu (fun sample => arms.sum (fun action =>
              (predictableLossAt loss 0 sample action) ^ 2)) := by
            simpa [predictableLossAt] using hsecondMap.symm
  | succ n =>
      let history := fun sample : Env × ((k : Nat) → Action × Real) =>
        (sample.1, Preorder.frestrictLe n sample.2)
      let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
        loss.successor n input.1 input.2
      have hhistory : Measurable history := measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)
      have hfirstMeas : Measurable (fun input => roundLoss input comparator) :=
        (loss.measurable_successor n).comp
          (measurable_fst.prodMk
            (measurable_snd.prodMk
              (measurable_const : Measurable
                (fun _ : Env × History.FinitePairHistory Action Real n => comparator))))
      have hsecondMeas : Measurable (fun input =>
          arms.sum (fun action => (roundLoss input action) ^ 2)) := by
        refine Finset.measurable_sum arms fun action _haction => ?_
        exact ((loss.measurable_successor n).comp
          (measurable_fst.prodMk
            (measurable_snd.prodMk
              (measurable_const : Measurable
                (fun _ : Env × History.FinitePairHistory Action Real n => action))))).pow_const 2
      have hcore := sampledPredictableObservedSuccessor_first_second_moment
        prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
          comparator hcomparator
      dsimp only at hcore
      constructor
      · calc
          integral mu (fun sample => observedImportanceWeightedLossAt
              arms eta gamma (n + 1) sample comparator) =
              integral (mu.map history) (fun input => roundLoss input comparator) := by
            simpa [mu, history, roundLoss, observedImportanceWeightedLossAt,
              sampledTrajectoryProbabilityAt] using hcore.1
          _ = integral mu (fun sample => predictableLossAt loss (n + 1)
              sample comparator) := by
            simpa [history, roundLoss, predictableLossAt] using
              (integral_map hhistory.aemeasurable hfirstMeas.aestronglyMeasurable)
      · calc
          integral mu (fun sample => observedMixedSquaredImportanceWeightedLossAt
              arms eta gamma (n + 1) sample) =
              integral (mu.map history) (fun input =>
                arms.sum (fun action => (roundLoss input action) ^ 2)) := by
            simpa [mu, history, roundLoss,
              observedMixedSquaredImportanceWeightedLossAt,
              sampledTrajectoryProbabilityAt] using hcore.2
          _ = integral mu (fun sample => arms.sum (fun action =>
              (predictableLossAt loss (n + 1) sample action) ^ 2)) := by
            simpa [history, roundLoss, predictableLossAt] using
              (integral_map hhistory.aemeasurable hsecondMeas.aestronglyMeasurable)

/-- Finite-horizon observed EXP3 first and mixed-second moments over
`t < horizon`; when the horizon is positive this range includes time zero. -/
theorem sampledPredictableObserved_finiteHorizon_first_second_moment
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    (integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        observedImportanceWeightedLossAt arms eta gamma t sample comparator)) =
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator))) ∧
    (integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        observedMixedSquaredImportanceWeightedLossAt arms eta gamma t sample)) =
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        arms.sum (fun action =>
          (predictableLossAt loss t sample action) ^ 2)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  have hobserved (t : Nat) := integrable_observedAt prior arms harms eta gamma
    hgamma_pos hgamma_le_one loss t comparator hcomparator
  have htrueFirst (t : Nat) := integrable_predictableLossAt
    mu loss t comparator
  have htrueSecond (t : Nat) := integrable_predictableLossSqSumAt
    mu arms loss t
  have hmoment (t : Nat) := sampledPredictableObservedAt_first_second_moment
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss t
      comparator hcomparator
  dsimp only at hobserved hmoment
  constructor
  · calc
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
          observedImportanceWeightedLossAt arms eta gamma t sample comparator)) =
          (Finset.range horizon).sum (fun t => integral mu (fun sample =>
            observedImportanceWeightedLossAt arms eta gamma t sample comparator)) := by
        exact ExpectationBochnerSums.integral_finset_sum mu (Finset.range horizon)
          (fun t sample => observedImportanceWeightedLossAt
            arms eta gamma t sample comparator)
          (fun t _ht => (hobserved t).1)
      _ = (Finset.range horizon).sum (fun t => integral mu (fun sample =>
          predictableLossAt loss t sample comparator)) := by
        apply Finset.sum_congr rfl
        intro t _ht
        exact (hmoment t).1
      _ = integral mu (fun sample => (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) := by
        symm
        exact ExpectationBochnerSums.integral_finset_sum mu (Finset.range horizon)
          (fun t sample => predictableLossAt loss t sample comparator)
          (fun t _ht => htrueFirst t)
  · calc
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
          observedMixedSquaredImportanceWeightedLossAt arms eta gamma t sample)) =
          (Finset.range horizon).sum (fun t => integral mu (fun sample =>
            observedMixedSquaredImportanceWeightedLossAt arms eta gamma t sample)) := by
        exact ExpectationBochnerSums.integral_finset_sum mu (Finset.range horizon)
          (fun t sample => observedMixedSquaredImportanceWeightedLossAt
            arms eta gamma t sample)
          (fun t _ht => (hobserved t).2)
      _ = (Finset.range horizon).sum (fun t => integral mu (fun sample =>
          arms.sum (fun action =>
            (predictableLossAt loss t sample action) ^ 2))) := by
        apply Finset.sum_congr rfl
        intro t _ht
        exact (hmoment t).2
      _ = integral mu (fun sample => (Finset.range horizon).sum (fun t =>
          arms.sum (fun action =>
            (predictableLossAt loss t sample action) ^ 2))) := by
        symm
        exact ExpectationBochnerSums.integral_finset_sum mu (Finset.range horizon)
          (fun t sample => arms.sum (fun action =>
            (predictableLossAt loss t sample action) ^ 2))
          (fun t _ht => htrueSecond t)

end Exp3
end BanditRLProof
