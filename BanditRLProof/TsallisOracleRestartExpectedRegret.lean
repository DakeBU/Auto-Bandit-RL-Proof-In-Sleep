import BanditRLProof.TsallisOracleRestartPredictableRegret
import BanditRLProof.TsallisScheduledExpectedRegret

/-!
# Expected-regret law transport for generated oracle restarts

This module transports predictable importance-weighted first moments under
the generated restart trajectory. The transport is performed on the actual
global law and therefore does not assume independent fresh epoch runs.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Predictable importance-weighted loss using the generated restart
probability at the same actual trajectory time. -/
noncomputable def sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    Action -> Real :=
  Exp3.importanceWeightedLoss
    (sampledOracleRestartHalfTsallisProbabilityAtTime
      arms harms eta schedule t sample)
    (Exp3.predictableLossAt loss t sample) (sample.2 t).1

/-- Stored-reward importance-weighted loss under the generated restart
probability at the same actual trajectory time. -/
noncomputable def sampledOracleRestartHalfTsallisObservedEstimatedLossAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    Action -> Real :=
  Exp3.importanceWeightedLoss
    (sampledOracleRestartHalfTsallisProbabilityAtTime
      arms harms eta schedule t sample)
    (fun _ => (sample.2 t).2) (sample.2 t).1

/-- Restarted successor probability on an environment/global-prefix state. -/
noncomputable def sampledOracleRestartHalfTsallisProbabilityAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (schedule : OracleRestartSchedule) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Action -> Real :=
  fun input =>
    sampledOracleRestartHalfTsallisHistoryDistribution
      arms harms eta schedule n input.2

/-- Environment-lifted measurable source for one restarted successor law. -/
noncomputable def sampledOracleRestartHalfTsallisEnvironmentHistoryDistributionSource
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    Exp3.MeasurableFiniteActionDistribution arms
      (sampledOracleRestartHalfTsallisProbabilityAt
        (Env := Env) arms harms eta schedule n) := by
  let localSource :=
    sampledOracleRestartHalfTsallisHistoryDistributionSource
      arms harms eta schedule n
  exact {
    distribution := fun input => localSource.distribution input.2
    measurable_prob := fun action haction =>
      (localSource.measurable_prob action haction).comp measurable_snd
  }

/-- The restarted policy comapped to the environment/global-prefix state. -/
noncomputable def sampledOracleRestartHalfTsallisPolicyAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    Kernel (Env × History.FinitePairHistory Action Real n) Action :=
  ((sampledOracleRestartHalfTsallisHistoryAlgorithm
    arms harms eta schedule).policy n).comap
      (fun input : Env × History.FinitePairHistory Action Real n => input.2)
      measurable_snd

instance instSampledOracleRestartHalfTsallisPolicyAtIsMarkov
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    IsMarkovKernel (sampledOracleRestartHalfTsallisPolicyAt
      (Env := Env) arms harms eta schedule n) := by
  unfold sampledOracleRestartHalfTsallisPolicyAt
  infer_instance

theorem sampledOracleRestartHalfTsallisPolicyAt_eq_finiteActionKernel
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    sampledOracleRestartHalfTsallisPolicyAt
        (Env := Env) arms harms eta schedule n =
      Exp3.finiteActionKernel arms
        (sampledOracleRestartHalfTsallisProbabilityAt
          (Env := Env) arms harms eta schedule n)
        (sampledOracleRestartHalfTsallisEnvironmentHistoryDistributionSource
          (Env := Env) arms harms eta schedule n) := by
  ext input event hevent
  rw [sampledOracleRestartHalfTsallisPolicyAt, Kernel.comap_apply,
    sampledOracleRestartHalfTsallisHistoryAlgorithm_policy,
    Exp3.finiteActionKernel_apply, Exp3.finiteActionKernel_apply]
  rfl

theorem measurable_sampledOracleRestartHalfTsallisProbabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (t : Nat) (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Real) =>
      sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta schedule t sample candidate) := by
  cases t with
  | zero => exact measurable_const
  | succ n =>
      exact
        ((sampledOracleRestartHalfTsallisHistoryDistributionSource
          arms harms eta schedule n).measurable_prob
            candidate hcandidate).comp
          ((Preorder.measurable_frestrictLe n).comp measurable_snd)

theorem measurable_sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (t : Nat) (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Real) =>
      sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
        arms harms eta schedule loss t sample candidate) := by
  unfold sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
    Exp3.importanceWeightedLoss
  refine Measurable.ite ?_
    ((Exp3.measurable_predictableLossAt loss t candidate).div
      (measurable_sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta schedule t candidate hcandidate)) measurable_const
  simpa only [Set.mem_setOf_eq] using
    (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))
      (measurableSet_singleton candidate)

/-- Deterministic predictable feedback identifies each stored-reward restart
estimator with its predictable counterpart almost surely. -/
theorem sampledOracleRestartHalfTsallisObservedEstimatedLossAt_eq_predictable_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (t : Nat) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    (fun sample =>
      sampledOracleRestartHalfTsallisObservedEstimatedLossAt
        arms harms eta schedule t sample) =ᵐ[mu]
      (fun sample =>
        sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
          arms harms eta schedule loss t sample) := by
  dsimp only
  let algorithm :=
    sampledOracleRestartHalfTsallisHistoryAlgorithm
      arms harms eta schedule
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  have hreward :
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 t).2) =ᵐ[mu]
      (fun sample =>
        Exp3.predictableLossAt loss t sample (sample.2 t).1) := by
    cases t with
    | zero =>
        simpa [mu, algorithm,
          sampledOracleRestartHalfTsallisTrajectoryKernel,
          Exp3.predictableLossAt] using
          (Exp3.canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
            prior algorithm loss)
    | succ n =>
        simpa [mu, algorithm, Exp3.predictableLossAt] using
          (Exp3.canonicalPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
            prior algorithm loss n)
  filter_upwards [hreward] with sample hsample
  funext candidate
  unfold sampledOracleRestartHalfTsallisObservedEstimatedLossAt
    sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
  by_cases hchosen : (sample.2 t).1 = candidate
  · simp [Exp3.importanceWeightedLoss, hchosen, hsample]
  · simp [Exp3.importanceWeightedLoss, hchosen]

/-- At each generated restart time, mixed and comparator-weighted
importance-weighted estimators are integrable and have the corresponding
predictable environment first moments. -/
theorem sampledOracleRestartHalfTsallisPredictableEstimatedLossAt_first_moments
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (hq : FTRL.finiteSimplex arms q) (t : Nat) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    (Integrable (fun sample =>
        FTRL.linearLoss arms
          (sampledOracleRestartHalfTsallisProbabilityAtTime
            arms harms eta schedule t sample)
          (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
            arms harms eta schedule loss t sample)) mu ∧
      Integrable (fun sample =>
        FTRL.linearLoss arms q
          (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
            arms harms eta schedule loss t sample)) mu) ∧
    ((integral mu (fun sample =>
        FTRL.linearLoss arms
          (sampledOracleRestartHalfTsallisProbabilityAtTime
            arms harms eta schedule t sample)
          (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
            arms harms eta schedule loss t sample)) =
      integral mu (fun sample =>
        FTRL.linearLoss arms
          (sampledOracleRestartHalfTsallisProbabilityAtTime
            arms harms eta schedule t sample)
          (Exp3.predictableLossAt loss t sample))) ∧
    (integral mu (fun sample =>
        FTRL.linearLoss arms q
          (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
            arms harms eta schedule loss t sample)) =
      integral mu (fun sample =>
        FTRL.linearLoss arms q
          (Exp3.predictableLossAt loss t sample)))) := by
  dsimp only
  let algorithm :=
    sampledOracleRestartHalfTsallisHistoryAlgorithm
      arms harms eta schedule
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  cases t with
  | zero =>
      let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
        sample.1
      let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 0).1
      let prob := fun _env : Env =>
        initialHalfTsallisDistribution arms harms (eta 0)
      let roundLoss := loss.initial
      let source := initialHalfTsallisEnvironmentDistributionSource
        (Env := Env) arms harms (eta 0)
      have hhistory : Measurable history := measurable_fst
      have haction : Measurable action :=
        measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
      have hkernel : Kernel.const Env algorithm.initialAction =
          Exp3.finiteActionKernel arms prob source := by
        ext env event hevent
        rw [Kernel.const_apply, Exp3.finiteActionKernel_apply]
        rfl
      have hcond : condDistrib action history mu =ᵐ[mu.map history]
          Exp3.finiteActionKernel arms prob source := by
        have hbase :=
          Exp3.canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
            prior algorithm loss.environment
        rw [hkernel] at hbase
        simpa [mu, algorithm, history, action,
          sampledOracleRestartHalfTsallisTrajectoryKernel] using hbase
      have hprobPos : forall env candidate, candidate ∈ arms ->
          0 < prob env candidate := by
        intro env candidate hcandidate
        exact isRegularizedMinimizer_pos arms (eta 0) (fun _ => 0)
          (initialHalfTsallisDistribution arms harms (eta 0))
          (halfTsallisMinimizer_isRegularizedMinimizer
            arms harms (eta 0) (fun _ => 0)) candidate hcandidate
      have hmoment :=
        integral_mixed_weightedImportanceWeightedLoss_eq_predictable
          mu history hhistory action haction arms prob roundLoss q hq source
          hcond hprobPos
          (fun candidate _hcandidate =>
            loss.measurable_initial.comp
              (measurable_id.prodMk measurable_const))
          (fun env candidate _hcandidate =>
            loss.initial_mem_unitInterval env candidate)
      have hintegrable :=
        integrable_mixed_weightedImportanceWeightedLoss_of_condDistrib
          mu history hhistory action haction arms prob roundLoss q hq source
          hcond hprobPos
          (fun candidate _hcandidate =>
            loss.measurable_initial.comp
              (measurable_id.prodMk measurable_const))
          (fun env candidate _hcandidate =>
            loss.initial_mem_unitInterval env candidate)
      constructor
      · simpa [history, action, prob, roundLoss,
          sampledOracleRestartHalfTsallisProbabilityAtTime,
          sampledOracleRestartHalfTsallisPredictableEstimatedLossAt,
          Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using
          hintegrable
      · simpa [history, action, prob, roundLoss,
          sampledOracleRestartHalfTsallisProbabilityAtTime,
          sampledOracleRestartHalfTsallisPredictableEstimatedLossAt,
          Exp3.predictableLossAt, Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using hmoment
  | succ n =>
      let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.1, Preorder.frestrictLe n sample.2)
      let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 (n + 1)).1
      let prob := sampledOracleRestartHalfTsallisProbabilityAt
        (Env := Env) arms harms eta schedule n
      let roundLoss := sampledScheduledHalfTsallisPredictableLossAt loss n
      let source :=
        sampledOracleRestartHalfTsallisEnvironmentHistoryDistributionSource
          (Env := Env) arms harms eta schedule n
      have hhistory : Measurable history :=
        measurable_fst.prodMk
          ((Preorder.measurable_frestrictLe n).comp measurable_snd)
      have haction : Measurable action :=
        measurable_fst.comp
          ((measurable_pi_apply (n + 1)).comp measurable_snd)
      have hcond : condDistrib action history mu =ᵐ[mu.map history]
          Exp3.finiteActionKernel arms prob source := by
        have hbase :=
          sampledOracleRestartHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
            prior arms harms eta schedule loss.environment n
        change condDistrib action history mu =ᵐ[mu.map history]
          sampledOracleRestartHalfTsallisPolicyAt
            (Env := Env) arms harms eta schedule n at hbase
        rw [sampledOracleRestartHalfTsallisPolicyAt_eq_finiteActionKernel
          (Env := Env) arms harms eta schedule n] at hbase
        simpa [mu, history, action, prob, source] using hbase
      have hprobPos : forall h candidate, candidate ∈ arms ->
          0 < prob h candidate := by
        intro h candidate hcandidate
        exact sampledOracleRestartHalfTsallisHistoryDistribution_pos
          arms harms eta schedule n h.2 candidate hcandidate
      have hmoment :=
        integral_mixed_weightedImportanceWeightedLoss_eq_predictable
          mu history hhistory action haction arms prob roundLoss q hq source
          hcond hprobPos
          (fun candidate _hcandidate =>
            measurable_sampledHalfTsallisPredictableLossAt
              loss n candidate)
          (fun h candidate _hcandidate =>
            loss.successor_mem_unitInterval n h.1 h.2 candidate)
      have hintegrable :=
        integrable_mixed_weightedImportanceWeightedLoss_of_condDistrib
          mu history hhistory action haction arms prob roundLoss q hq source
          hcond hprobPos
          (fun candidate _hcandidate =>
            measurable_sampledHalfTsallisPredictableLossAt
              loss n candidate)
          (fun h candidate _hcandidate =>
            loss.successor_mem_unitInterval n h.1 h.2 candidate)
      constructor
      · simpa [history, action, prob, roundLoss,
          sampledOracleRestartHalfTsallisProbabilityAtTime,
          sampledOracleRestartHalfTsallisPredictableEstimatedLossAt,
          Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using
          hintegrable
      · simpa [history, action, prob, roundLoss,
          sampledOracleRestartHalfTsallisProbabilityAtTime,
          sampledOracleRestartHalfTsallisPredictableEstimatedLossAt,
          Exp3.predictableLossAt, Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using hmoment

theorem finiteSimplex_sampledOracleRestartHalfTsallisProbabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    FTRL.finiteSimplex arms
      (sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta schedule t sample) := by
  cases t with
  | zero =>
      exact ⟨
        (finiteActionDistribution_initialHalfTsallisDistribution
          arms harms (eta 0)).nonneg,
        (finiteActionDistribution_initialHalfTsallisDistribution
          arms harms (eta 0)).sum_eq_one⟩
  | succ n =>
      let source :=
        sampledOracleRestartHalfTsallisHistoryDistributionSource
          arms harms eta schedule n
      exact ⟨
        (source.distribution
          (Preorder.frestrictLe n sample.2)).nonneg,
        (source.distribution
          (Preorder.frestrictLe n sample.2)).sum_eq_one⟩

/-- Generated restart mixed predictable loss and any fixed simplex
comparator loss are integrable at every actual time. -/
theorem integrable_sampledOracleRestartHalfTsallisPredictableLinearLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (hq : FTRL.finiteSimplex arms q) (t : Nat) :
    Integrable (fun sample =>
        FTRL.linearLoss arms
          (sampledOracleRestartHalfTsallisProbabilityAtTime
            arms harms eta schedule t sample)
          (Exp3.predictableLossAt loss t sample)) mu ∧
      Integrable (fun sample =>
        FTRL.linearLoss arms q
          (Exp3.predictableLossAt loss t sample)) mu := by
  have hprobMeas (candidate : Action) (hcandidate : candidate ∈ arms) :=
    measurable_sampledOracleRestartHalfTsallisProbabilityAtTime
      (Env := Env) arms harms eta schedule t candidate hcandidate
  have hlossMeas (candidate : Action) :=
    Exp3.measurable_predictableLossAt loss t candidate
  have hcurrentMeas : Measurable (fun sample =>
      FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (Exp3.predictableLossAt loss t sample)) := by
    unfold FTRL.linearLoss
    exact Finset.measurable_sum arms fun candidate hcandidate =>
      (hprobMeas candidate hcandidate).mul (hlossMeas candidate)
  have hcomparatorMeas : Measurable (fun sample =>
      FTRL.linearLoss arms q
        (Exp3.predictableLossAt loss t sample)) := by
    unfold FTRL.linearLoss
    exact Finset.measurable_sum arms fun candidate _hcandidate =>
      measurable_const.mul (hlossMeas candidate)
  have hlossMem (sample : Env × ((k : Nat) -> Action × Real))
      (candidate : Action) :
      Exp3.predictableLossAt loss t sample candidate ∈
        Set.Icc (0 : Real) 1 := by
    cases t with
    | zero => exact loss.initial_mem_unitInterval sample.1 candidate
    | succ n =>
        exact loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) candidate
  have hcurrentMem (sample : Env × ((k : Nat) -> Action × Real)) :
      FTRL.linearLoss arms
          (sampledOracleRestartHalfTsallisProbabilityAtTime
            arms harms eta schedule t sample)
          (Exp3.predictableLossAt loss t sample) ∈
        Set.Icc (0 : Real) 1 := by
    let p := sampledOracleRestartHalfTsallisProbabilityAtTime
      arms harms eta schedule t sample
    have hp :=
      finiteSimplex_sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta schedule t sample
    constructor
    · unfold FTRL.linearLoss
      exact Finset.sum_nonneg fun candidate hcandidate =>
        mul_nonneg (hp.1 candidate hcandidate)
          (hlossMem sample candidate).1
    · calc
        FTRL.linearLoss arms p
            (Exp3.predictableLossAt loss t sample) <= arms.sum p := by
          unfold FTRL.linearLoss
          exact Finset.sum_le_sum fun candidate hcandidate => by
            nlinarith [hp.1 candidate hcandidate,
              (hlossMem sample candidate).2]
        _ = 1 := hp.2
  have hcomparatorMem (sample : Env × ((k : Nat) -> Action × Real)) :
      FTRL.linearLoss arms q
          (Exp3.predictableLossAt loss t sample) ∈
        Set.Icc (0 : Real) 1 := by
    constructor
    · unfold FTRL.linearLoss
      exact Finset.sum_nonneg fun candidate hcandidate =>
        mul_nonneg (hq.1 candidate hcandidate)
          (hlossMem sample candidate).1
    · calc
        FTRL.linearLoss arms q
            (Exp3.predictableLossAt loss t sample) <= arms.sum q := by
          unfold FTRL.linearLoss
          exact Finset.sum_le_sum fun candidate hcandidate => by
            nlinarith [hq.1 candidate hcandidate,
              (hlossMem sample candidate).2]
        _ = 1 := hq.2
  constructor
  · refine Integrable.of_bound hcurrentMeas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun sample => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hcurrentMem sample).1]
      exact (hcurrentMem sample).2
  · refine Integrable.of_bound hcomparatorMeas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun sample => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hcomparatorMem sample).1]
      exact (hcomparatorMem sample).2

/-- Estimated regret contributed by one actual schedule epoch. -/
noncomputable def sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon epoch : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (oracleRestartEpochRounds schedule.start horizon epoch).sum (fun t =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
          arms harms eta schedule loss t sample) -
      FTRL.linearLoss arms q
        (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
          arms harms eta schedule loss t sample))

/-- Stored-reward estimated regret contributed by one actual schedule
epoch. -/
noncomputable def sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (q : Action -> Real) (horizon epoch : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (oracleRestartEpochRounds schedule.start horizon epoch).sum (fun t =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (sampledOracleRestartHalfTsallisObservedEstimatedLossAt
          arms harms eta schedule t sample) -
      FTRL.linearLoss arms q
        (sampledOracleRestartHalfTsallisObservedEstimatedLossAt
          arms harms eta schedule t sample))

/-- Environment regret against a fixed comparator distribution on one actual
schedule epoch. -/
noncomputable def sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon epoch : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (oracleRestartEpochRounds schedule.start horizon epoch).sum (fun t =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (Exp3.predictableLossAt loss t sample) -
      FTRL.linearLoss arms q
        (Exp3.predictableLossAt loss t sample))

/-- Epoch-local estimated regret is integrable and has exactly the same
integral as fixed-comparator environment regret on the actual generated
restart law. -/
theorem integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_eq_environmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (hq : FTRL.finiteSimplex arms q)
    (horizon epoch : Nat) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
          arms harms eta schedule loss q horizon epoch) mu ∧
      Integrable
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
          arms harms eta schedule loss q horizon epoch) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
            arms harms eta schedule loss q horizon epoch) =
        integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
            arms harms eta schedule loss q horizon epoch) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let estimatedTerm := fun t sample =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
          arms harms eta schedule loss t sample) -
      FTRL.linearLoss arms q
        (sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
          arms harms eta schedule loss t sample)
  let environmentTerm := fun t sample =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (Exp3.predictableLossAt loss t sample) -
      FTRL.linearLoss arms q
        (Exp3.predictableLossAt loss t sample)
  have hmoment (t : Nat) :=
    sampledOracleRestartHalfTsallisPredictableEstimatedLossAt_first_moments
      prior arms harms eta schedule loss q hq t
  dsimp only at hmoment
  have hestimatedTerm (t : Nat) : Integrable (estimatedTerm t) mu :=
    (hmoment t).1.1.sub (hmoment t).1.2
  have henvironmentParts (t : Nat) :=
    integrable_sampledOracleRestartHalfTsallisPredictableLinearLossAt
      mu arms harms eta schedule loss q hq t
  have henvironmentTerm (t : Nat) : Integrable (environmentTerm t) mu :=
    (henvironmentParts t).1.sub (henvironmentParts t).2
  have hestimatedSum : Integrable
      (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
        arms harms eta schedule loss q horizon epoch) mu := by
    unfold
      sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
    exact IntegrabilitySums.integrable_finset_sum mu
      (oracleRestartEpochRounds schedule.start horizon epoch)
      estimatedTerm (fun t _ht => hestimatedTerm t)
  have henvironmentSum : Integrable
      (sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
        arms harms eta schedule loss q horizon epoch) mu := by
    unfold
      sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
    exact IntegrabilitySums.integrable_finset_sum mu
      (oracleRestartEpochRounds schedule.start horizon epoch)
      environmentTerm (fun t _ht => henvironmentTerm t)
  refine ⟨hestimatedSum, henvironmentSum, ?_⟩
  calc
    integral mu
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
          arms harms eta schedule loss q horizon epoch) =
      (oracleRestartEpochRounds schedule.start horizon epoch).sum (fun t =>
        integral mu (estimatedTerm t)) := by
      unfold
        sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
      exact ExpectationBochnerSums.integral_finset_sum mu
        (oracleRestartEpochRounds schedule.start horizon epoch)
        estimatedTerm (fun t _ht => hestimatedTerm t)
    _ = (oracleRestartEpochRounds schedule.start horizon epoch).sum (fun t =>
        integral mu (environmentTerm t)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [integral_sub (hmoment t).1.1 (hmoment t).1.2,
        integral_sub (henvironmentParts t).1 (henvironmentParts t).2,
        (hmoment t).2.1, (hmoment t).2.2]
    _ = integral mu
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
          arms harms eta schedule loss q horizon epoch) := by
      symm
      unfold
        sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
      exact ExpectationBochnerSums.integral_finset_sum mu
        (oracleRestartEpochRounds schedule.start horizon epoch)
        environmentTerm (fun t _ht => henvironmentTerm t)

/-- Stored-reward and predictable-estimator regret agree almost surely on
every actual schedule epoch fiber. -/
theorem sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_eq_predictable_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon epoch : Nat) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        arms harms eta schedule q horizon epoch =ᵐ[mu]
      sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
        arms harms eta schedule loss q horizon epoch := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  have hestimatedAll : ∀ᵐ sample ∂mu, ∀ t,
      sampledOracleRestartHalfTsallisObservedEstimatedLossAt
          arms harms eta schedule t sample =
        sampledOracleRestartHalfTsallisPredictableEstimatedLossAt
          arms harms eta schedule loss t sample := by
    rw [ae_all_iff]
    intro t
    exact
      sampledOracleRestartHalfTsallisObservedEstimatedLossAt_eq_predictable_ae
        prior arms harms eta schedule loss t
  filter_upwards [hestimatedAll] with sample hsample
  unfold
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
    sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
  apply Finset.sum_congr rfl
  intro t _ht
  rw [hsample t]

/-- A point-mass comparator on one schedule fiber is the existing
epoch-comparator environment-regret surface. -/
theorem sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret_pointMass_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (epoch : Nat)
    (hcomparator : epochComparator epoch ∈ arms)
    (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
        arms harms eta schedule loss (pointMass (epochComparator epoch))
        horizon epoch sample =
      sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
        arms harms eta schedule loss epochComparator horizon epoch sample := by
  unfold
    sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
    sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
  apply Finset.sum_congr rfl
  intro t ht
  have hstart : schedule.start t = epoch :=
    (Finset.mem_filter.mp ht).2
  rw [linearLoss_pointMass arms hcomparator]
  simp [hstart]

/-- Fixed-arm epoch estimated regret transports exactly to the existing
epoch environment-regret integral on the generated restart law. -/
theorem integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (epoch : Nat)
    (hcomparator : epochComparator epoch ∈ arms)
    (horizon : Nat) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
          arms harms eta schedule loss
          (pointMass (epochComparator epoch)) horizon epoch) mu ∧
      Integrable
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
            arms harms eta schedule loss
            (pointMass (epochComparator epoch)) horizon epoch) =
        integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
            arms harms eta schedule loss epochComparator horizon epoch) := by
  dsimp only
  have h :=
    integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_eq_environmentRegret
      prior arms harms eta schedule loss
      (pointMass (epochComparator epoch))
      (finiteSimplex_pointMass arms hcomparator) horizon epoch
  dsimp only at h
  have hpoint :
      sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret
          arms harms eta schedule loss
          (pointMass (epochComparator epoch)) horizon epoch =
        sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch := by
    funext sample
    exact
      sampledOracleRestartHalfTsallisPredictableScheduleEpochEnvironmentRegret_pointMass_eq
        arms harms eta schedule loss epochComparator epoch hcomparator
        horizon sample
  rw [hpoint] at h
  exact h

/-- Stored-reward fixed-arm epoch estimated regret is integrable and has
exactly the existing epoch environment-regret integral. -/
theorem integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (epoch : Nat)
    (hcomparator : epochComparator epoch ∈ arms)
    (horizon : Nat) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
          arms harms eta schedule
          (pointMass (epochComparator epoch)) horizon epoch) mu ∧
      Integrable
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
            arms harms eta schedule
            (pointMass (epochComparator epoch)) horizon epoch) =
        integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
            arms harms eta schedule loss epochComparator horizon epoch) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  have hpredictable :=
    integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
      prior arms harms eta schedule loss epochComparator epoch hcomparator
      horizon
  dsimp only at hpredictable
  have hae :=
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_eq_predictable_ae
      prior arms harms eta schedule loss
      (pointMass (epochComparator epoch)) horizon epoch
  dsimp only at hae
  have hobserved : Integrable
      (sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        arms harms eta schedule
        (pointMass (epochComparator epoch)) horizon epoch) mu := by
    simpa [mu] using hpredictable.1.congr hae.symm
  refine ⟨hobserved, ?_, ?_⟩
  · simpa [mu] using hpredictable.2.1
  · exact (integral_congr_ae hae).trans hpredictable.2.2

/-- Any expected estimated-regret certificate on an actual schedule epoch
transports to the corresponding fixed-arm environment-regret certificate. -/
theorem integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret_le_of_estimatedRegret_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (epoch : Nat)
    (hcomparator : epochComparator epoch ∈ arms)
    (horizon : Nat) (bound : Real)
    (hEstimated :
      let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
        arms harms eta schedule loss.environment
      integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
            arms harms eta schedule loss
            (pointMass (epochComparator epoch)) horizon epoch) <= bound) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    integral mu
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch) <=
      bound := by
  dsimp only at hEstimated ⊢
  have htransport :=
    integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
      prior arms harms eta schedule loss epochComparator epoch hcomparator
      horizon
  dsimp only at htransport
  rw [← htransport.2.2]
  exact hEstimated

/-- Epoch-local expected estimated-regret certificates assemble into an
expected moving-comparator square-root bound on the actual generated restart
trajectory. -/
theorem integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSqrt_of_epochEstimatedRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action)
    (horizon : Nat)
    (hcomparator : ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
      epochComparator epoch ∈ arms)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (hEstimated :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        integral
            (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
              arms harms eta schedule loss.environment)
            (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
              arms harms eta schedule loss
              (pointMass (epochComparator epoch)) horizon epoch) <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds
                schedule.start horizon epoch).card : Real)) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms eta schedule loss
          (fun t => epochComparator (schedule.start t)) horizon) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
            arms harms eta schedule loss
            (fun t => epochComparator (schedule.start t)) horizon) <=
        coefficient *
            Real.sqrt
              ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
          Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  have hEpochTransport
      (epoch : Nat)
      (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon) :=
    integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
      prior arms harms eta schedule loss epochComparator epoch
      (hcomparator epoch hepoch) horizon
  have hEpochIntegrable
      (epoch : Nat)
      (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon) :
      Integrable
        (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch) mu := by
    simpa [mu] using (hEpochTransport epoch hepoch).2.1
  have hEpochIntegralLe
      (epoch : Nat)
      (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon) :
      integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
            arms harms eta schedule loss epochComparator horizon epoch) <=
        coefficient *
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real) := by
    have hEq := (hEpochTransport epoch hepoch).2.2
    rw [← hEq]
    simpa [mu] using hEstimated epoch hepoch
  have hsum : Integrable (fun sample =>
      (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
        sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch
          sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu
      (oracleRestartScheduleEpochs schedule horizon)
      (fun epoch sample =>
        sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch sample)
      hEpochIntegrable
  have hdecomp :
      sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms eta schedule loss
          (fun t => epochComparator (schedule.start t)) horizon =
        fun sample =>
          (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
            sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
              arms harms eta schedule loss epochComparator horizon epoch
              sample) := by
    funext sample
    exact
      sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_sum_scheduleEpochRegret
        arms harms eta schedule loss epochComparator horizon sample
  have hmoving : Integrable
      (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta schedule loss
        (fun t => epochComparator (schedule.start t)) horizon) mu := by
    rw [hdecomp]
    exact hsum
  refine ⟨hmoving, ?_⟩
  calc
    integral mu
        (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms eta schedule loss
          (fun t => epochComparator (schedule.start t)) horizon) =
      (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
        integral mu
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
            arms harms eta schedule loss epochComparator horizon epoch)) := by
      rw [hdecomp]
      exact ExpectationBochnerSums.integral_finset_sum mu
        (oracleRestartScheduleEpochs schedule horizon)
        (fun epoch sample =>
          sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
            arms harms eta schedule loss epochComparator horizon epoch sample)
        hEpochIntegrable
    _ <= (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
        coefficient *
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real)) := by
      exact Finset.sum_le_sum hEpochIntegralLe
    _ = coefficient *
        (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real)) := by
      rw [Finset.mul_sum]
    _ <= coefficient *
        (Real.sqrt
            ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
          Real.sqrt (((horizon + 1 : Nat) : Real))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_sqrt_oracleRestartEpochRounds_card_le
          (oracleRestartScheduleEpochs schedule horizon)
          schedule.start horizon
          (fun t ht =>
            oracleRestartSchedule_start_mem_epochs schedule horizon t ht))
        hcoefficient
    _ = coefficient *
          Real.sqrt
            ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by ring

/-- Switch-count-facing expected restart bound under an explicit cardinality
contract and epoch-local estimated-regret certificates. -/
theorem integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSwitchCountSqrt_of_epochEstimatedRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action)
    (horizon switches : Nat)
    (hcomparator : ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
      epochComparator epoch ∈ arms)
    (hEpochCard :
      (oracleRestartScheduleEpochs schedule horizon).card <= switches + 1)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (hEstimated :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        integral
            (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
              arms harms eta schedule loss.environment)
            (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
              arms harms eta schedule loss
              (pointMass (epochComparator epoch)) horizon epoch) <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds
                schedule.start horizon epoch).card : Real)) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms eta schedule loss
          (fun t => epochComparator (schedule.start t)) horizon) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
            arms harms eta schedule loss
            (fun t => epochComparator (schedule.start t)) horizon) <=
        coefficient * Real.sqrt (((switches + 1 : Nat) : Real)) *
          Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  dsimp only
  have hrestart :=
    integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSqrt_of_epochEstimatedRegret
      prior arms harms eta schedule loss epochComparator horizon hcomparator
      coefficient hcoefficient hEstimated
  dsimp only at hrestart
  refine ⟨hrestart.1, ?_⟩
  have hcardReal :
      ((oracleRestartScheduleEpochs schedule horizon).card : Real) <=
        (((switches + 1 : Nat) : Real)) := by
    exact_mod_cast hEpochCard
  have hsqrt :
      Real.sqrt
          ((oracleRestartScheduleEpochs schedule horizon).card : Real) <=
        Real.sqrt (((switches + 1 : Nat) : Real)) :=
    Real.sqrt_le_sqrt hcardReal
  calc
    _ <= coefficient *
          Real.sqrt
            ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := hrestart.2
    _ <= coefficient * Real.sqrt (((switches + 1 : Nat) : Real)) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt hcoefficient)
        (Real.sqrt_nonneg _)

/-- Stored-reward epoch certificates assemble into the same expected
moving-comparator square-root bound on the actual generated restart
trajectory. -/
theorem integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSqrt_of_epochObservedEstimatedRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action)
    (horizon : Nat)
    (hcomparator : ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
      epochComparator epoch ∈ arms)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (hObserved :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        integral
            (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
              arms harms eta schedule loss.environment)
            (sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
              arms harms eta schedule
              (pointMass (epochComparator epoch)) horizon epoch) <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds
                schedule.start horizon epoch).card : Real)) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms eta schedule loss
          (fun t => epochComparator (schedule.start t)) horizon) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
            arms harms eta schedule loss
            (fun t => epochComparator (schedule.start t)) horizon) <=
        coefficient *
            Real.sqrt
              ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
          Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  have hEstimated
      (epoch : Nat)
      (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon) :
      integral
          (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
            arms harms eta schedule loss.environment)
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
            arms harms eta schedule loss
            (pointMass (epochComparator epoch)) horizon epoch) <=
        coefficient *
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real) := by
    have hpredictable :=
      integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
        prior arms harms eta schedule loss epochComparator epoch
        (hcomparator epoch hepoch) horizon
    have hobserved :=
      integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
        prior arms harms eta schedule loss epochComparator epoch
        (hcomparator epoch hepoch) horizon
    dsimp only at hpredictable hobserved
    rw [hpredictable.2.2, ← hobserved.2.2]
    exact hObserved epoch hepoch
  exact
    integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSqrt_of_epochEstimatedRegret
      prior arms harms eta schedule loss epochComparator horizon hcomparator
      coefficient hcoefficient hEstimated

/-- Stored-reward epoch certificates imply the switch-count-facing expected
restart bound under the explicit schedule-cardinality contract. -/
theorem integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSwitchCountSqrt_of_epochObservedEstimatedRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action)
    (horizon switches : Nat)
    (hcomparator : ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
      epochComparator epoch ∈ arms)
    (hEpochCard :
      (oracleRestartScheduleEpochs schedule horizon).card <= switches + 1)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (hObserved :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        integral
            (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
              arms harms eta schedule loss.environment)
            (sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
              arms harms eta schedule
              (pointMass (epochComparator epoch)) horizon epoch) <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds
                schedule.start horizon epoch).card : Real)) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms eta schedule loss
          (fun t => epochComparator (schedule.start t)) horizon) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
            arms harms eta schedule loss
            (fun t => epochComparator (schedule.start t)) horizon) <=
        coefficient * Real.sqrt (((switches + 1 : Nat) : Real)) *
          Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  have hEstimated
      (epoch : Nat)
      (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon) :
      integral
          (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
            arms harms eta schedule loss.environment)
          (sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret
            arms harms eta schedule loss
            (pointMass (epochComparator epoch)) horizon epoch) <=
        coefficient *
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real) := by
    have hpredictable :=
      integral_sampledOracleRestartHalfTsallisPredictableScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
        prior arms harms eta schedule loss epochComparator epoch
        (hcomparator epoch hepoch) horizon
    have hobserved :=
      integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
        prior arms harms eta schedule loss epochComparator epoch
        (hcomparator epoch hepoch) horizon
    dsimp only at hpredictable hobserved
    rw [hpredictable.2.2, ← hobserved.2.2]
    exact hObserved epoch hepoch
  exact
    integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSwitchCountSqrt_of_epochEstimatedRegret
      prior arms harms eta schedule loss epochComparator horizon switches
      hcomparator hEpochCard coefficient hcoefficient hEstimated

end Tsallis
end BanditRLProof
