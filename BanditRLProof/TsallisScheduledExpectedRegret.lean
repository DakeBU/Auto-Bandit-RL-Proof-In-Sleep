import BanditRLProof.TsallisScheduledAllRateExpectedStability
import BanditRLProof.TsallisFTRLEstimatedEnvironmentRegret

/-!
# Expected regret for generated scheduled half-Tsallis FTRL

This module transports the observed importance-weighted regret of the
scheduled half-Tsallis trajectory to predictable environment regret.  It then
combines the pathwise time-varying penalty theorem with the all-rate expected
stability theorem.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Predictable importance-weighted loss using the scheduled probability at
the same actual trajectory time. -/
noncomputable def sampledScheduledHalfTsallisPredictableEstimatedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    Action -> Real :=
  Exp3.importanceWeightedLoss
    (sampledScheduledHalfTsallisProbabilityAtTime arms harms eta t sample)
    (Exp3.predictableLossAt loss t sample) (sample.2 t).1

/-- Predictable environment regret of the scheduled generated probabilities
against a fixed comparator through the inclusive terminal time. -/
noncomputable def sampledScheduledHalfTsallisPredictableEnvironmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (Exp3.predictableLossAt loss t sample) -
      FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample))

/-- Finite-horizon scheduled regret after replacing stored rewards by the
predictable importance-weighted loss vectors. -/
noncomputable def sampledScheduledHalfTsallisPredictableEstimatedRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (sampledScheduledHalfTsallisPredictableEstimatedLossAt
          arms harms eta loss t sample) -
      FTRL.linearLoss arms q
        (sampledScheduledHalfTsallisPredictableEstimatedLossAt
          arms harms eta loss t sample))

theorem measurable_sampledScheduledHalfTsallisProbabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Real) =>
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample candidate) := by
  cases t with
  | zero => exact measurable_const
  | succ n =>
      exact
        (measurable_halfTsallisMinimizer_comp
          arms harms (eta (n + 1))
          (sampledScheduledHalfTsallisHistoryScore arms harms eta n)
          (fun selected hselected =>
            measurable_sampledScheduledHalfTsallisHistoryScore
              arms harms eta
              (canonicalHalfTsallisScheduleFiniteHistorySelectorMeasurability
                arms harms eta) n selected hselected)
          candidate hcandidate).comp
            ((Preorder.measurable_frestrictLe n).comp measurable_snd)

theorem measurable_sampledScheduledHalfTsallisPredictableEstimatedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (t : Nat) (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Real) =>
      sampledScheduledHalfTsallisPredictableEstimatedLossAt
        arms harms eta loss t sample candidate) := by
  unfold sampledScheduledHalfTsallisPredictableEstimatedLossAt
    Exp3.importanceWeightedLoss
  refine Measurable.ite ?_
    ((Exp3.measurable_predictableLossAt loss t candidate).div
      (measurable_sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t candidate hcandidate)) measurable_const
  simpa only [Set.mem_setOf_eq] using
    (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))
      (measurableSet_singleton candidate)

/-- Deterministic predictable feedback identifies each stored-reward
scheduled estimator with its predictable counterpart almost surely. -/
theorem sampledScheduledHalfTsallisObservedEstimatedLossAt_eq_predictable_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (t : Nat) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    (fun sample => sampledScheduledHalfTsallisObservedEstimatedLossAt
      arms harms eta t sample) =ᵐ[mu]
      (fun sample => sampledScheduledHalfTsallisPredictableEstimatedLossAt
        arms harms eta loss t sample) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hreward :
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 t).2) =ᵐ[mu]
      (fun sample => Exp3.predictableLossAt loss t sample (sample.2 t).1) := by
    cases t with
    | zero =>
        simpa [mu, selector, sampledScheduledHalfTsallisTrajectoryKernel,
          Exp3.predictableLossAt] using
          (Exp3.canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
            prior
              (sampledScheduledHalfTsallisHistoryAlgorithm
                arms harms eta selector.finiteHistory)
              loss)
    | succ n =>
        simpa [mu, selector, Exp3.predictableLossAt] using
          (Exp3.canonicalPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
            prior
              (sampledScheduledHalfTsallisHistoryAlgorithm
                arms harms eta selector.finiteHistory)
              loss n)
  filter_upwards [hreward] with sample hsample
  funext candidate
  unfold sampledScheduledHalfTsallisObservedEstimatedLossAt
    sampledScheduledHalfTsallisPredictableEstimatedLossAt
  by_cases hchosen : (sample.2 t).1 = candidate
  · simp [Exp3.importanceWeightedLoss, hchosen, hsample]
  · simp [Exp3.importanceWeightedLoss, hchosen]

/-- At each scheduled time, the mixed and comparator-weighted predictable IW
estimators are integrable and have their corresponding environment first
moments. -/
theorem sampledScheduledHalfTsallisPredictableEstimatedLossAt_first_moments
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (hq : FTRL.finiteSimplex arms q) (t : Nat) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    (Integrable (fun sample =>
        FTRL.linearLoss arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample)
          (sampledScheduledHalfTsallisPredictableEstimatedLossAt
            arms harms eta loss t sample)) mu ∧
      Integrable (fun sample =>
        FTRL.linearLoss arms q
          (sampledScheduledHalfTsallisPredictableEstimatedLossAt
            arms harms eta loss t sample)) mu) ∧
    ((integral mu (fun sample =>
        FTRL.linearLoss arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample)
          (sampledScheduledHalfTsallisPredictableEstimatedLossAt
            arms harms eta loss t sample)) =
      integral mu (fun sample =>
        FTRL.linearLoss arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample)
          (Exp3.predictableLossAt loss t sample))) ∧
    (integral mu (fun sample =>
        FTRL.linearLoss arms q
          (sampledScheduledHalfTsallisPredictableEstimatedLossAt
            arms harms eta loss t sample)) =
      integral mu (fun sample =>
        FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample)))) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let algorithm := sampledScheduledHalfTsallisHistoryAlgorithm
    arms harms eta selector.finiteHistory
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  cases t with
  | zero =>
      let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
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
          sampledScheduledHalfTsallisTrajectoryKernel] using hbase
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
          sampledScheduledHalfTsallisProbabilityAtTime,
          sampledScheduledHalfTsallisPredictableEstimatedLossAt,
          Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using hintegrable
      · simpa [history, action, prob, roundLoss,
          sampledScheduledHalfTsallisProbabilityAtTime,
          sampledScheduledHalfTsallisPredictableEstimatedLossAt,
          Exp3.predictableLossAt, Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using hmoment
  | succ n =>
      let history := sampledScheduledHalfTsallisHistoryAt
        (Env := Env) (Action := Action) n
      let action := sampledScheduledHalfTsallisActionAt
        (Env := Env) (Action := Action) n
      let prob := sampledScheduledHalfTsallisProbabilityAt
        (Env := Env) arms harms eta n
      let roundLoss := sampledScheduledHalfTsallisPredictableLossAt loss n
      let source := sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta selector.finiteHistory n
      have hhistory : Measurable history :=
        measurable_fst.prodMk
          ((Preorder.measurable_frestrictLe n).comp measurable_snd)
      have haction : Measurable action :=
        measurable_fst.comp ((measurable_pi_apply (n + 1)).comp measurable_snd)
      have hcond : condDistrib action history mu =ᵐ[mu.map history]
          Exp3.finiteActionKernel arms prob source := by
        have hbase :=
          sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
            prior arms harms eta selector.finiteHistory loss.environment n
        change condDistrib action history mu =ᵐ[mu.map history]
          sampledScheduledHalfTsallisPolicyAt (Env := Env)
            arms harms eta selector.finiteHistory n at hbase
        rw [sampledScheduledHalfTsallisPolicyAt_eq_finiteActionKernel
          (Env := Env) arms harms eta selector.finiteHistory n] at hbase
        simpa [mu, history, action, prob, source] using hbase
      have hprobPos : forall h candidate, candidate ∈ arms ->
          0 < prob h candidate := by
        intro h candidate hcandidate
        exact isRegularizedMinimizer_pos arms (eta (n + 1))
          (sampledScheduledHalfTsallisScoreAt arms harms eta n h)
          (prob h)
          (halfTsallisMinimizer_isRegularizedMinimizer
            arms harms (eta (n + 1))
              (sampledScheduledHalfTsallisScoreAt arms harms eta n h))
          candidate hcandidate
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
          sampledScheduledHalfTsallisProbabilityAtTime,
          sampledScheduledHalfTsallisPredictableEstimatedLossAt,
          Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using hintegrable
      · simpa [history, action, prob, roundLoss,
          sampledScheduledHalfTsallisProbabilityAtTime,
          sampledScheduledHalfTsallisPredictableEstimatedLossAt,
          Exp3.predictableLossAt, Exp3.mixedImportanceWeightedLoss,
          Exp3.weightedImportanceWeightedLoss, FTRL.linearLoss] using hmoment

theorem finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    FTRL.finiteSimplex arms
      (sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample) := by
  cases t with
  | zero =>
      exact ⟨
        (finiteActionDistribution_initialHalfTsallisDistribution
          arms harms (eta 0)).nonneg,
        (finiteActionDistribution_initialHalfTsallisDistribution
          arms harms (eta 0)).sum_eq_one⟩
  | succ n =>
      exact (halfTsallisMinimizer_isRegularizedMinimizer arms harms
        (eta (n + 1))
        (sampledScheduledHalfTsallisHistoryScore arms harms eta n
          (Preorder.frestrictLe n sample.2))).1

/-- Current scheduled mixed predictable loss and a fixed-comparator
predictable loss are integrable at every actual time. -/
theorem integrable_sampledScheduledHalfTsallisPredictableLinearLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (hq : FTRL.finiteSimplex arms q) (t : Nat) :
    Integrable (fun sample =>
        FTRL.linearLoss arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample)
          (Exp3.predictableLossAt loss t sample)) mu ∧
      Integrable (fun sample =>
        FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample)) mu := by
  have hprobMeas (candidate : Action) (hcandidate : candidate ∈ arms) :=
    measurable_sampledScheduledHalfTsallisProbabilityAtTime
      (Env := Env) arms harms eta t candidate hcandidate
  have hlossMeas (candidate : Action) :=
    Exp3.measurable_predictableLossAt loss t candidate
  have hcurrentMeas : Measurable (fun sample =>
      FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (Exp3.predictableLossAt loss t sample)) := by
    unfold FTRL.linearLoss
    exact Finset.measurable_sum arms fun candidate hcandidate =>
      (hprobMeas candidate hcandidate).mul (hlossMeas candidate)
  have hcomparatorMeas : Measurable (fun sample =>
      FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample)) := by
    unfold FTRL.linearLoss
    exact Finset.measurable_sum arms fun candidate _hcandidate =>
      measurable_const.mul (hlossMeas candidate)
  have hlossMem (sample : Env × ((k : Nat) -> Action × Real))
      (candidate : Action) :
      Exp3.predictableLossAt loss t sample candidate ∈ Set.Icc (0 : Real) 1 := by
    cases t with
    | zero => exact loss.initial_mem_unitInterval sample.1 candidate
    | succ n =>
        exact loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) candidate
  have hcurrentMem (sample : Env × ((k : Nat) -> Action × Real)) :
      FTRL.linearLoss arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample)
          (Exp3.predictableLossAt loss t sample) ∈ Set.Icc (0 : Real) 1 := by
    let p := sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample
    have hp := finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample
    constructor
    · unfold FTRL.linearLoss
      exact Finset.sum_nonneg fun candidate hcandidate =>
        mul_nonneg (hp.1 candidate hcandidate) (hlossMem sample candidate).1
    · calc
        FTRL.linearLoss arms p (Exp3.predictableLossAt loss t sample) <=
            arms.sum p := by
          unfold FTRL.linearLoss
          exact Finset.sum_le_sum fun candidate hcandidate => by
            nlinarith [hp.1 candidate hcandidate,
              (hlossMem sample candidate).2]
        _ = 1 := hp.2
  have hcomparatorMem (sample : Env × ((k : Nat) -> Action × Real)) :
      FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample) ∈
        Set.Icc (0 : Real) 1 := by
    constructor
    · unfold FTRL.linearLoss
      exact Finset.sum_nonneg fun candidate hcandidate =>
        mul_nonneg (hq.1 candidate hcandidate) (hlossMem sample candidate).1
    · calc
        FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample) <=
            arms.sum q := by
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

/-- Predictable scheduled estimated regret is integrable and has exactly the
same finite-horizon integral as predictable environment regret. -/
theorem integral_sampledScheduledHalfTsallisPredictableEstimatedRegret_eq_environmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (hq : FTRL.finiteSimplex arms q)
    (horizon : Nat) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (sampledScheduledHalfTsallisPredictableEstimatedRegret
        arms harms eta loss q horizon) mu ∧
      Integrable (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss q horizon) mu ∧
      integral mu (sampledScheduledHalfTsallisPredictableEstimatedRegret
        arms harms eta loss q horizon) =
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss q horizon) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let estimatedTerm := fun t sample =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (sampledScheduledHalfTsallisPredictableEstimatedLossAt
          arms harms eta loss t sample) -
      FTRL.linearLoss arms q
        (sampledScheduledHalfTsallisPredictableEstimatedLossAt
          arms harms eta loss t sample)
  let environmentTerm := fun t sample =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (Exp3.predictableLossAt loss t sample) -
      FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample)
  have hmoment (t : Nat) :=
    sampledScheduledHalfTsallisPredictableEstimatedLossAt_first_moments
      prior arms harms eta loss q hq t
  dsimp only at hmoment
  have hestimatedTerm (t : Nat) : Integrable (estimatedTerm t) mu :=
    (hmoment t).1.1.sub (hmoment t).1.2
  have henvironmentParts (t : Nat) :=
    integrable_sampledScheduledHalfTsallisPredictableLinearLossAt
      mu arms harms eta loss q hq t
  have henvironmentTerm (t : Nat) : Integrable (environmentTerm t) mu :=
    (henvironmentParts t).1.sub (henvironmentParts t).2
  have hestimatedSum : Integrable
      (sampledScheduledHalfTsallisPredictableEstimatedRegret
        arms harms eta loss q horizon) mu := by
    unfold sampledScheduledHalfTsallisPredictableEstimatedRegret
    exact IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (horizon + 1)) estimatedTerm
      (fun t _ht => hestimatedTerm t)
  have henvironmentSum : Integrable
      (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss q horizon) mu := by
    unfold sampledScheduledHalfTsallisPredictableEnvironmentRegret
    exact IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (horizon + 1)) environmentTerm
      (fun t _ht => henvironmentTerm t)
  refine ⟨hestimatedSum, henvironmentSum, ?_⟩
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEstimatedRegret
        arms harms eta loss q horizon) =
        (Finset.range (horizon + 1)).sum (fun t =>
          integral mu (estimatedTerm t)) := by
      unfold sampledScheduledHalfTsallisPredictableEstimatedRegret
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (horizon + 1)) estimatedTerm
        (fun t _ht => hestimatedTerm t)
    _ = (Finset.range (horizon + 1)).sum (fun t =>
          integral mu (environmentTerm t)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [integral_sub (hmoment t).1.1 (hmoment t).1.2,
        integral_sub (henvironmentParts t).1 (henvironmentParts t).2,
        (hmoment t).2.1, (hmoment t).2.2]
    _ = integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss q horizon) := by
      symm
      unfold sampledScheduledHalfTsallisPredictableEnvironmentRegret
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (horizon + 1)) environmentTerm
        (fun t _ht => henvironmentTerm t)

/-- Observed scheduled estimated regret agrees almost surely with the
predictable-estimator version over every finite horizon. -/
theorem sampledScheduledHalfTsallisEstimatedRegret_eq_predictable_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon : Nat) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta q horizon =ᵐ[mu]
      sampledScheduledHalfTsallisPredictableEstimatedRegret
        arms harms eta loss q horizon := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hestimatedAll : ∀ᵐ sample ∂mu, ∀ t,
      sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta t sample =
        sampledScheduledHalfTsallisPredictableEstimatedLossAt
          arms harms eta loss t sample := by
    rw [ae_all_iff]
    intro t
    exact sampledScheduledHalfTsallisObservedEstimatedLossAt_eq_predictable_ae
      prior arms harms eta loss t
  filter_upwards [hestimatedAll] with sample hsample
  unfold sampledScheduledHalfTsallisEstimatedRegret
    sampledScheduledHalfTsallisPredictableEstimatedRegret
  apply Finset.sum_congr rfl
  intro t _ht
  rw [hsample t]

/-- Observed scheduled IW regret is integrable and has exactly the predictable
environment-regret integral. -/
theorem integral_sampledScheduledHalfTsallisEstimatedRegret_eq_environmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (hq : FTRL.finiteSimplex arms q)
    (horizon : Nat) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta q horizon) mu ∧
      Integrable (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss q horizon) mu ∧
      integral mu (sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta q horizon) =
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss q horizon) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hpredictable :=
    integral_sampledScheduledHalfTsallisPredictableEstimatedRegret_eq_environmentRegret
      prior arms harms eta loss q hq horizon
  dsimp only at hpredictable
  have hae :=
    sampledScheduledHalfTsallisEstimatedRegret_eq_predictable_ae
      prior arms harms eta loss q horizon
  dsimp only at hae
  have hobserved : Integrable
      (sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta q horizon) mu :=
    hpredictable.1.congr hae.symm
  exact ⟨hobserved, hpredictable.2.1,
    (integral_congr_ae hae).trans hpredictable.2.2⟩

/-!
The theorem below is the generated-trajectory scheduled regret endpoint of
this module.  The rate schedule is only required to be positive on the finite
horizon and nonincreasing between included rounds.  Each stability term uses
the refined branch when its local rate is at most `1 / 2`, and the compiled
constant-one fallback otherwise.
-/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_allRateBound
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (heta : forall t, t <= horizon -> 0 < eta t)
    (hetaMono : forall t, t < horizon -> eta (t + 1) <= eta t) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) <=
      integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) +
        halfTsallisPotentialMass arms
          (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
        1 / eta horizon := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let stabilitySum := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    (Finset.range (horizon + 1)).sum (fun t =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample t)
  let allRateSum := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    (Finset.range (horizon + 1)).sum (fun t =>
      sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
        arms harms eta sample t)
  let penalty :=
    halfTsallisPotentialMass arms
        (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
      1 / eta horizon
  let rhs := fun (sample : Env × ((k : Nat) -> Action × Real)) =>
    stabilitySum sample + penalty
  haveI : IsProbabilityMeasure mu := inferInstance
  have hq : FTRL.finiteSimplex arms (pointMass best) :=
    finiteSimplex_pointMass arms hbest
  have hmoment :=
    integral_sampledScheduledHalfTsallisEstimatedRegret_eq_environmentRegret
      prior arms harms eta loss (pointMass best) hq horizon
  dsimp only at hmoment
  have hstabilityIntegrable :=
    integrable_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_allRate
      prior horizon arms harms eta heta loss
  dsimp only at hstabilityIntegrable
  have hstabilityIntegrable' : Integrable stabilitySum mu := by
    simpa [stabilitySum, mu, selector] using hstabilityIntegrable.1
  have hallRateIntegrable : Integrable allRateSum mu := by
    simpa [allRateSum, mu, selector] using hstabilityIntegrable.2
  have hrhsIntegrable : Integrable rhs mu := by
    unfold rhs
    exact hstabilityIntegrable'.add (integrable_const _)
  have hpathwise : ∀ᵐ sample ∂mu,
      sampledScheduledHalfTsallisEstimatedRegret
          arms harms eta (pointMass best) horizon sample <= rhs sample := by
    filter_upwards [] with sample
    have hbase :=
      sampledScheduledHalfTsallisEstimatedRegret_pointMass_le_stability_add_penalty
        arms harms eta sample hbest horizon heta hetaMono
    unfold rhs stabilitySum penalty
    simp only [sampledScheduledHalfTsallisProbabilityAtTime] at hbase
    linarith
  have hintegrated := integral_mono_ae hmoment.1 hrhsIntegrable hpathwise
  have hrhsIntegral : integral mu rhs = integral mu stabilitySum + penalty := by
    unfold rhs
    rw [integral_add hstabilityIntegrable' (integrable_const _)]
    simp
  have hstabilityBoundBase :=
    integral_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
      prior horizon arms harms eta heta loss
  dsimp only at hstabilityBoundBase
  have hstabilityBound : integral mu stabilitySum <= integral mu allRateSum := by
    simpa [mu, selector, stabilitySum, allRateSum] using hstabilityBoundBase
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) =
        integral mu (sampledScheduledHalfTsallisEstimatedRegret
          arms harms eta (pointMass best) horizon) := hmoment.2.2.symm
    _ <= integral mu rhs := hintegrated
    _ = integral mu stabilitySum + penalty := hrhsIntegral
    _ <= integral mu allRateSum + penalty := by
      linarith
    _ = integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
          sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
            arms harms eta sample t)) +
          halfTsallisPotentialMass arms
            (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
          1 / eta horizon := by
      unfold allRateSum penalty
      ring

end Tsallis
end BanditRLProof
