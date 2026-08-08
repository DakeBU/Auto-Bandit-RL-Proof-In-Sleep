import BanditRLProof.Exp3ExplorationBias

/-!
# Integrated predictable EXP3 bridge

This module connects the pathwise sampled-Hedge inequality to the generated
predictable trajectory moments.  The key law transport uses the exploration
distribution `p_t` to sample an action while a distinct predictable pure-Hedge
distribution `q_t` weights the importance-weighted estimator.

The route is: construct measurable `q_t` sources, prove cross-weighted score
regularity, transport the conditional action law, aggregate over a finite
horizon, and only then integrate the almost-sure Hedge inequality.
-/

namespace BanditRLProof
namespace Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The pure exponential-weights probability used by Hedge at an actual
sampled-trajectory time. -/
noncomputable def sampledTrajectoryPureProbabilityAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Action -> Real :=
  distribution arms eta
    (sampledTrajectoryObservedLoss arms eta gamma sample) t

/-- Measurable finite-distribution source for the pure Hedge probabilities at
every actual trajectory time. -/
noncomputable def sampledTrajectoryPureProbabilitySourceAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (t : Nat) :
    MeasurableFiniteActionDistribution arms
      (sampledTrajectoryPureProbabilityAt (Env := Env) arms eta gamma t) := by
  refine
    { distribution := fun sample =>
        { nonneg := fun action _haction =>
            distribution_nonneg arms harms eta
              (sampledTrajectoryObservedLoss arms eta gamma sample) t action
          sum_eq_one := sum_distribution arms harms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t }
      measurable_prob := ?_ }
  intro action haction
  cases t with
  | zero =>
      simp [sampledTrajectoryPureProbabilityAt, distribution, totalWeight,
        weight, cumulativeLoss]
  | succ n =>
      have hmeas := measurable_normalizedHistoryDistribution arms eta
        (sampledHistoryScore arms eta gamma n)
        (fun selected hselected =>
          MeasurableFiniteHistoryScore.measurable_score
            (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
            n selected hselected)
        action haction
      simpa [sampledTrajectoryPureProbabilityAt,
        distribution_sampledTrajectoryObservedLoss_succ] using
        hmeas.comp ((Preorder.measurable_frestrictLe n).comp measurable_snd)

/-- Pure-Hedge predictable loss at one actual trajectory time. -/
noncomputable def sampledTrajectoryPurePredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  arms.sum (fun action =>
    sampledTrajectoryPureProbabilityAt arms eta gamma t sample action *
      predictableLossAt loss t sample action)

/-- Exploration-mixed predictable loss at one actual trajectory time. -/
noncomputable def sampledTrajectoryExploredPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  arms.sum (fun action =>
    sampledTrajectoryProbabilityAt arms eta gamma t sample action *
      predictableLossAt loss t sample action)

/-- The pure-Hedge mixed observed estimator at one actual trajectory time. -/
noncomputable def sampledTrajectoryPureObservedLossAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  mixedLoss arms eta
    (sampledTrajectoryObservedLoss arms eta gamma sample) t

theorem measurable_sampledTrajectoryPurePredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable (sampledTrajectoryPurePredictableLossAt
      arms eta gamma loss t) := by
  unfold sampledTrajectoryPurePredictableLossAt
  refine Finset.measurable_sum arms fun action haction => ?_
  exact
    ((sampledTrajectoryPureProbabilitySourceAt (Env := Env) arms harms
      eta gamma t).measurable_prob action haction).mul
      (measurable_predictableLossAt loss t action)

theorem sampledTrajectoryPurePredictableLossAt_mem_unitInterval
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample ∈
      Set.Icc (0 : Real) 1 := by
  let source := sampledTrajectoryPureProbabilitySourceAt (Env := Env)
    arms harms eta gamma t
  have hloss (action : Action) :
      predictableLossAt loss t sample action ∈ Set.Icc (0 : Real) 1 := by
    cases t with
    | zero => exact loss.initial_mem_unitInterval sample.1 action
    | succ n =>
        exact loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) action
  constructor
  · exact Finset.sum_nonneg fun action haction =>
      mul_nonneg ((source.distribution sample).nonneg action haction)
        (hloss action).1
  · calc
      sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample <=
          arms.sum (fun action =>
            sampledTrajectoryPureProbabilityAt arms eta gamma t sample action *
              1) := by
        apply Finset.sum_le_sum
        intro action haction
        exact mul_le_mul_of_nonneg_left (hloss action).2
          ((source.distribution sample).nonneg action haction)
      _ = 1 := by
        simpa using (source.distribution sample).sum_eq_one

theorem integrable_sampledTrajectoryPurePredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (loss : PredictableLossVector Env Action) (t : Nat) :
    Integrable (sampledTrajectoryPurePredictableLossAt
      arms eta gamma loss t) mu := by
  refine Integrable.of_bound
    (measurable_sampledTrajectoryPurePredictableLossAt arms harms eta gamma
      loss t).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun sample => by
    have hmem := sampledTrajectoryPurePredictableLossAt_mem_unitInterval
      arms harms eta gamma loss t sample
    simpa [Real.norm_eq_abs, abs_of_nonneg hmem.1] using hmem.2

theorem measurable_sampledTrajectoryExploredPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable (sampledTrajectoryExploredPredictableLossAt
      arms eta gamma loss t) := by
  unfold sampledTrajectoryExploredPredictableLossAt
  refine Finset.measurable_sum arms fun action haction => ?_
  exact
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_nonneg hgamma_le_one t).measurable_prob action haction).mul
      (measurable_predictableLossAt loss t action)

theorem sampledTrajectoryExploredPredictableLossAt_mem_unitInterval
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledTrajectoryExploredPredictableLossAt arms eta gamma loss t sample ∈
      Set.Icc (0 : Real) 1 := by
  let source := sampledTrajectoryProbabilitySourceAt (Env := Env)
    arms harms eta gamma hgamma_nonneg hgamma_le_one t
  have hloss (action : Action) :
      predictableLossAt loss t sample action ∈ Set.Icc (0 : Real) 1 := by
    cases t with
    | zero => exact loss.initial_mem_unitInterval sample.1 action
    | succ n =>
        exact loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) action
  constructor
  · exact Finset.sum_nonneg fun action haction =>
      mul_nonneg ((source.distribution sample).nonneg action haction)
        (hloss action).1
  · calc
      sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample <=
        arms.sum (fun action =>
          sampledTrajectoryProbabilityAt arms eta gamma t sample action * 1) := by
        apply Finset.sum_le_sum
        intro action haction
        exact mul_le_mul_of_nonneg_left (hloss action).2
          ((source.distribution sample).nonneg action haction)
      _ = 1 := by
        simpa using (source.distribution sample).sum_eq_one

theorem integrable_sampledTrajectoryExploredPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Integrable (sampledTrajectoryExploredPredictableLossAt
      arms eta gamma loss t) mu := by
  refine Integrable.of_bound
    (measurable_sampledTrajectoryExploredPredictableLossAt arms harms eta gamma
      hgamma_nonneg hgamma_le_one loss t).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun sample => by
    have hmem := sampledTrajectoryExploredPredictableLossAt_mem_unitInterval
      arms harms eta gamma hgamma_nonneg hgamma_le_one loss t sample
    simpa [Real.norm_eq_abs, abs_of_nonneg hmem.1] using hmem.2

/-- The observed scalar reward can be replaced almost surely by its selected
predictable coordinate inside the pure-Hedge mixed estimator. -/
theorem sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    (fun sample => sampledTrajectoryPureObservedLossAt
        arms eta gamma t sample) =ᵐ[mu]
      (fun sample => weightedImportanceWeightedLoss arms
        (sampledTrajectoryProbabilityAt arms eta gamma t sample)
        (sampledTrajectoryPureProbabilityAt arms eta gamma t sample)
        (predictableLossAt loss t sample) (sample.2 t).1) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  have hreward :
      (fun sample : Env × ((k : Nat) -> Action × Real) => (sample.2 t).2) =ᵐ[mu]
        (fun sample => predictableLossAt loss t sample (sample.2 t).1) := by
    cases t with
    | zero =>
        simpa [mu, predictableLossAt,
          sampledImportanceWeightedTrajectoryKernel] using
          (canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
            prior
              (sampledImportanceWeightedHistoryAlgorithm arms harms eta gamma
                hgamma_nonneg hgamma_le_one)
              loss)
    | succ n =>
        simpa [mu, predictableLossAt] using
          (sampledPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
            prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)
  filter_upwards [hreward] with sample hsample
  unfold sampledTrajectoryPureObservedLossAt mixedLoss
    weightedImportanceWeightedLoss
  apply Finset.sum_congr rfl
  intro action _haction
  change
    distribution arms eta
          (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
        sampledTrajectoryObservedLoss arms eta gamma sample t action =
      distribution arms eta
          (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
        importanceWeightedLoss
          (sampledTrajectoryProbabilityAt arms eta gamma t sample)
          (predictableLossAt loss t sample) (sample.2 t).1 action
  congr 1
  unfold sampledTrajectoryObservedLoss observedImportanceWeightedLossAt
  by_cases hchosen : (sample.2 t).1 = action
  · simp [importanceWeightedLoss, hchosen, hsample]
  · simp [importanceWeightedLoss, hchosen]

/-- The pure-Hedge observed mixed estimator is integrable on the generated
trajectory law. -/
theorem integrable_sampledTrajectoryPureObservedLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Integrable (sampledTrajectoryPureObservedLossAt arms eta gamma t) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let prob := sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t
  let weight := sampledTrajectoryPureProbabilityAt (Env := Env)
    arms eta gamma t
  let roundLoss := predictableLossAt loss t
  let probSource := sampledTrajectoryProbabilitySourceAt (Env := Env)
    arms harms eta gamma hgamma_pos.le hgamma_le_one t
  let weightSource := sampledTrajectoryPureProbabilitySourceAt (Env := Env)
    arms harms eta gamma t
  let regularity := sampledPredictableTrajectoryLossRegularityAt arms harms
    eta gamma hgamma_pos hgamma_le_one loss t
  have hchosen : Measurable
      (fun sample : Env × ((k : Nat) -> Action × Real) => (sample.2 t).1) := by
    fun_prop
  have hlatent : Integrable (fun sample =>
      weightedImportanceWeightedLoss arms (prob sample) (weight sample)
        (roundLoss sample) (sample.2 t).1) mu :=
    integrable_weightedImportanceWeightedLoss_selected_of_isFiniteMeasure
      mu arms prob weight roundLoss probSource weightSource
        (gamma / (arms.card : Real)) regularity
        (fun sample => (sample.2 t).1) hchosen
  have hae := sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss t
  dsimp only at hae
  exact hlatent.congr hae.symm

/-- At time zero, the pure-Hedge mixed observed estimator has the same
integral as the pure-Hedge predictable loss. -/
theorem sampledPredictablePureObservedInitial_integral_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    integral mu (sampledTrajectoryPureObservedLossAt arms eta gamma 0) =
      integral mu
        (sampledTrajectoryPurePredictableLossAt arms eta gamma loss 0) := by
  dsimp only
  let algorithm := sampledImportanceWeightedHistoryAlgorithm arms harms
    eta gamma hgamma_pos.le hgamma_le_one
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let prob := fun _env : Env => initialExploredDistribution arms eta gamma
  let weight := fun _env : Env =>
    distribution arms eta (fun _t _action => (0 : Real)) 0
  let roundLoss := loss.initial
  let probSource := sampledInitialEnvironmentDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
  let weightSource : MeasurableFiniteActionDistribution arms weight :=
    { distribution := fun _env =>
        { nonneg := fun selected _hselected =>
            distribution_nonneg arms harms eta
              (fun _t _action => (0 : Real)) 0 selected
          sum_eq_one := sum_distribution arms harms eta
            (fun _t _action => (0 : Real)) 0 }
      measurable_prob := fun _selected _hselected => measurable_const }
  let policy := finiteActionKernel arms prob probSource
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
  have hscore : Measurable (fun z : Env × Action =>
      weightedImportanceWeightedLoss arms (prob z.1) (weight z.1)
        (roundLoss z.1) z.2) :=
    measurable_weightedImportanceWeightedLoss_score arms prob weight roundLoss
      probSource weightSource epsilon hregularity
  have hintegrable : Integrable (fun z : Env × Action =>
      weightedImportanceWeightedLoss arms (prob z.1) (weight z.1)
        (roundLoss z.1) z.2) (mu.map history ⊗ₘ policy) := by
    rw [hhistoryMarginal]
    exact integrable_weightedImportanceWeightedLoss_score prior arms
      prob weight roundLoss probSource weightSource epsilon hregularity
  have hvector :=
    integral_weightedImportanceWeightedLoss_eq_integral_weightedLoss_of_condDistrib
      mu history hhistory action haction arms prob weight roundLoss
      probSource.distribution (fun env selected hselected =>
        hregularity.prob_pos env selected hselected)
      policy hpolicy hcond hscore hintegrable
  rw [hhistoryMarginal] at hvector
  have hae := sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss 0
  dsimp only at hae
  calc
    integral mu (sampledTrajectoryPureObservedLossAt arms eta gamma 0) =
        integral mu (fun sample =>
          weightedImportanceWeightedLoss arms (prob (history sample))
            (weight (history sample)) (roundLoss (history sample))
            (action sample)) := by
      apply integral_congr_ae
      simpa [prob, weight, roundLoss, history, action,
        sampledTrajectoryProbabilityAt, sampledTrajectoryPureProbabilityAt,
        distribution, totalWeight, weight, cumulativeLoss] using hae
    _ = integral prior (fun env =>
        arms.sum (fun selected => weight env selected * roundLoss env selected)) :=
      hvector
    _ = integral mu
        (sampledTrajectoryPurePredictableLossAt arms eta gamma loss 0) := by
      have hmeas : Measurable (fun env =>
          arms.sum (fun selected => weight env selected * roundLoss env selected)) := by
        refine Finset.measurable_sum arms fun selected hselected => ?_
        exact (weightSource.measurable_prob selected hselected).mul
          (loss.measurable_initial.comp
            (measurable_id.prodMk
              (measurable_const : Measurable (fun _ : Env => selected))))
      have hmap := integral_map (μ := mu) hhistory.aemeasurable
        hmeas.aestronglyMeasurable
      rw [hhistoryMarginal] at hmap
      have hpure :
          (fun sample => arms.sum (fun selected =>
            weight (history sample) selected *
              roundLoss (history sample) selected)) =
            sampledTrajectoryPurePredictableLossAt
              arms eta gamma loss 0 := by
        funext sample
        unfold sampledTrajectoryPurePredictableLossAt
        apply Finset.sum_congr rfl
        intro selected _hselected
        congr 1
      rw [← hpure]
      simpa only [Function.comp_apply] using hmap

/-- At a successor time, the pure-Hedge mixed observed estimator has the same
integral as the pure-Hedge predictable loss. -/
theorem sampledPredictablePureObservedSuccessor_integral_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    integral mu
        (sampledTrajectoryPureObservedLossAt arms eta gamma (n + 1)) =
      integral mu
        (sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss (n + 1)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 (n + 1)).1
  let prob := fun input : Env × History.FinitePairHistory Action Real n =>
    sampledHistoryDistribution arms eta gamma n input.2
  let weight := fun input : Env × History.FinitePairHistory Action Real n =>
    normalizedHistoryDistribution arms eta
      (sampledHistoryScore arms eta gamma n) input.2
  let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
    loss.successor n input.1 input.2
  let localProbSource := exploredHistoryDistributionSource arms harms eta gamma
    (sampledHistoryScore arms eta gamma)
    (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
    hgamma_pos.le hgamma_le_one n
  let probSource := sampledEnvironmentHistoryDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
  let localWeightSource := normalizedHistoryDistributionSource arms harms eta
    (sampledHistoryScore arms eta gamma)
    (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma) n
  let weightSource : MeasurableFiniteActionDistribution arms weight :=
    { distribution := fun input => localWeightSource.distribution input.2
      measurable_prob := fun selected hselected =>
        (localWeightSource.measurable_prob selected hselected).comp measurable_snd }
  let policy : Kernel
      (Env × History.FinitePairHistory Action Real n) Action :=
    (finiteActionKernel arms
      (sampledHistoryDistribution arms eta gamma n) localProbSource).comap
        (fun input : Env × History.FinitePairHistory Action Real n => input.2)
        measurable_snd
  let epsilon := gamma / (arms.card : Real)
  have hhistory : Measurable history :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action := by fun_prop
  have hregularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob roundLoss epsilon := by
    simpa [prob, roundLoss, epsilon] using
      (sampledPredictableSuccessorLossRegularity arms harms eta gamma
        hgamma_pos hgamma_le_one loss n)
  have hpolicyEq : policy = finiteActionKernel arms prob probSource := by
    ext input event hevent
    rw [Kernel.comap_apply, finiteActionKernel_apply,
      finiteActionKernel_apply]
  have hpolicy : policy =ᵐ[mu.map history]
      fun input => finiteActionMeasure arms (prob input) := by
    filter_upwards [] with input
    rw [hpolicyEq, finiteActionKernel_apply]
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    simpa [mu, history, action, policy, localProbSource] using
      (sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss n)
  have hscore : Measurable
      (fun z : (Env × History.FinitePairHistory Action Real n) × Action =>
        weightedImportanceWeightedLoss arms (prob z.1) (weight z.1)
          (roundLoss z.1) z.2) :=
    measurable_weightedImportanceWeightedLoss_score arms prob weight roundLoss
      probSource weightSource epsilon hregularity
  have hintegrable : Integrable
      (fun z : (Env × History.FinitePairHistory Action Real n) × Action =>
        weightedImportanceWeightedLoss arms (prob z.1) (weight z.1)
          (roundLoss z.1) z.2) (mu.map history ⊗ₘ policy) := by
    rw [hpolicyEq]
    exact integrable_weightedImportanceWeightedLoss_score (mu.map history)
      arms prob weight roundLoss probSource weightSource epsilon hregularity
  have hvector :=
    integral_weightedImportanceWeightedLoss_eq_integral_weightedLoss_of_condDistrib
      mu history hhistory action haction arms prob weight roundLoss
      probSource.distribution (fun input selected hselected =>
        hregularity.prob_pos input selected hselected)
      policy hpolicy hcond hscore hintegrable
  have hae := sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss (n + 1)
  dsimp only at hae
  calc
    integral mu
        (sampledTrajectoryPureObservedLossAt arms eta gamma (n + 1)) =
      integral mu (fun sample =>
        weightedImportanceWeightedLoss arms (prob (history sample))
          (weight (history sample)) (roundLoss (history sample))
          (action sample)) := by
      apply integral_congr_ae
      filter_upwards [hae] with sample hsample
      have hweight :
          sampledTrajectoryPureProbabilityAt arms eta gamma (n + 1) sample =
            weight (history sample) := by
        funext selected
        exact distribution_sampledTrajectoryObservedLoss_succ
          arms eta gamma sample n selected
      rw [hweight] at hsample
      simpa [prob, roundLoss, history, action,
        sampledTrajectoryProbabilityAt, predictableLossAt] using hsample
    _ = integral (mu.map history) (fun input =>
        arms.sum (fun selected => weight input selected *
          roundLoss input selected)) := hvector
    _ = integral mu
        (sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss (n + 1)) := by
      have hmeas : Measurable (fun input =>
          arms.sum (fun selected =>
            weight input selected * roundLoss input selected)) := by
        refine Finset.measurable_sum arms fun selected hselected => ?_
        exact (weightSource.measurable_prob selected hselected).mul
          ((loss.measurable_successor n).comp
            (measurable_fst.prodMk
              (measurable_snd.prodMk
                (measurable_const : Measurable
                  (fun _ : Env × History.FinitePairHistory Action Real n =>
                    selected)))))
      have hmap := integral_map (μ := mu) hhistory.aemeasurable
        hmeas.aestronglyMeasurable
      have hpure :
          (fun sample => arms.sum (fun selected =>
            weight (history sample) selected *
              roundLoss (history sample) selected)) =
            sampledTrajectoryPurePredictableLossAt
              arms eta gamma loss (n + 1) := by
        funext sample
        unfold sampledTrajectoryPurePredictableLossAt
        apply Finset.sum_congr rfl
        intro selected _hselected
        rw [show weight (history sample) selected =
            sampledTrajectoryPureProbabilityAt arms eta gamma (n + 1)
              sample selected by
          exact (distribution_sampledTrajectoryObservedLoss_succ
            arms eta gamma sample n selected).symm]
        rfl
      rw [← hpure]
      simpa only [Function.comp_apply] using hmap

/-- Every actual time satisfies the adaptive pure-Hedge first-moment
identity. -/
theorem sampledPredictablePureObservedAt_integral_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    integral mu (sampledTrajectoryPureObservedLossAt arms eta gamma t) =
      integral mu
        (sampledTrajectoryPurePredictableLossAt arms eta gamma loss t) := by
  cases t with
  | zero =>
      exact sampledPredictablePureObservedInitial_integral_eq
        prior arms harms eta gamma hgamma_pos hgamma_le_one loss
  | succ n =>
      exact sampledPredictablePureObservedSuccessor_integral_eq
        prior arms harms eta gamma hgamma_pos hgamma_le_one loss n

/-- The adaptive pure-Hedge first-moment identity summed over a finite
horizon. -/
theorem sampledPredictablePureObserved_finiteHorizon_integral_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPureObservedLossAt arms eta gamma t sample)) =
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss t sample)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  calc
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPureObservedLossAt arms eta gamma t sample)) =
      (Finset.range horizon).sum (fun t => integral mu
        (sampledTrajectoryPureObservedLossAt arms eta gamma t)) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon)
        (fun t sample =>
          sampledTrajectoryPureObservedLossAt arms eta gamma t sample)
        (fun t _ht => integrable_sampledTrajectoryPureObservedLossAt
          prior arms harms eta gamma hgamma_pos hgamma_le_one loss t)
    _ = (Finset.range horizon).sum (fun t => integral mu
        (sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss t)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact sampledPredictablePureObservedAt_integral_eq
        prior arms harms eta gamma hgamma_pos hgamma_le_one loss t
    _ = integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss t sample)) := by
      symm
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon)
        (fun t sample => sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss t sample)
        (fun t _ht => integrable_sampledTrajectoryPurePredictableLossAt
          mu arms harms eta gamma loss t)

/-- The a.e. sampled-Hedge inequality with its pure estimator-square term
replaced by the exploration-mixed square. -/
theorem sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    ∀ᵐ sample ∂mu,
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryPureObservedLossAt arms eta gamma t sample) -
        (Finset.range horizon).sum (fun t =>
          observedImportanceWeightedLossAt
            arms eta gamma t sample comparator) <=
      Real.log arms.card / eta +
        (eta * (1 / (1 - gamma))) *
          (Finset.range horizon).sum (fun t =>
            observedMixedSquaredImportanceWeightedLossAt
              arms eta gamma t sample) := by
  dsimp only
  have hhedge := sampledPredictableTrajectoryMeasure_hedge_regret_le_ae
    prior arms harms eta gamma heta hgamma_pos.le hgamma_lt_one.le
      loss horizon comparator hcomparator
  dsimp only at hhedge
  filter_upwards [hhedge] with sample hsample
  have hsecond :=
    (sampledTrajectory_finiteHorizon_explorationBias_secondMoment
      arms harms eta gamma hgamma_pos.le hgamma_lt_one loss horizon sample).2
  calc
    (Finset.range horizon).sum (fun t =>
          sampledTrajectoryPureObservedLossAt arms eta gamma t sample) -
        (Finset.range horizon).sum (fun t =>
          observedImportanceWeightedLossAt
            arms eta gamma t sample comparator) =
      (Finset.range horizon).sum (fun t =>
          mixedLoss arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t) -
        cumulativeLoss
          (sampledTrajectoryObservedLoss arms eta gamma sample)
          horizon comparator := by
      rfl
    _ <= Real.log arms.card / eta + eta *
        (Finset.range horizon).sum (fun t =>
          mixedSquaredLoss arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t) := hsample
    _ <= Real.log arms.card / eta +
        (eta * (1 / (1 - gamma))) *
          (Finset.range horizon).sum (fun t =>
            observedMixedSquaredImportanceWeightedLossAt
              arms eta gamma t sample) := by
      have hmul := mul_le_mul_of_nonneg_left hsecond heta.le
      nlinarith

/-- Integrated sampled-Hedge control with the exploration-mixed second moment
on the generated predictable trajectory law. -/
theorem sampledPredictable_integral_pureHedge_le_exploredSecondMoment
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPureObservedLossAt arms eta gamma t sample)) -
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        observedImportanceWeightedLossAt
          arms eta gamma t sample comparator)) <=
      Real.log arms.card / eta +
        (eta * (1 / (1 - gamma))) *
          integral mu (fun sample => (Finset.range horizon).sum (fun t =>
            observedMixedSquaredImportanceWeightedLossAt
              arms eta gamma t sample)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  have hpure (t : Nat) := integrable_sampledTrajectoryPureObservedLossAt
    prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss t
  have hobserved (t : Nat) := integrable_observedAt prior arms harms eta gamma
    hgamma_pos hgamma_lt_one.le loss t comparator hcomparator
  dsimp only at hpure hobserved
  have hpureSum : Integrable (fun sample => (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPureObservedLossAt arms eta gamma t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => sampledTrajectoryPureObservedLossAt
        arms eta gamma t sample) (fun t _ht => hpure t)
  have hcompSum : Integrable (fun sample => (Finset.range horizon).sum (fun t =>
      observedImportanceWeightedLossAt
        arms eta gamma t sample comparator)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => observedImportanceWeightedLossAt
        arms eta gamma t sample comparator) (fun t _ht => (hobserved t).1)
  have hsecondSum : Integrable (fun sample => (Finset.range horizon).sum (fun t =>
      observedMixedSquaredImportanceWeightedLossAt
        arms eta gamma t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => observedMixedSquaredImportanceWeightedLossAt
        arms eta gamma t sample) (fun t _ht => (hobserved t).2)
  have hae :=
    sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss horizon
        comparator hcomparator
  dsimp only at hae
  have hmono := integral_mono_ae (hpureSum.sub hcompSum)
    ((integrable_const _).add
      (hsecondSum.const_mul (eta * (1 / (1 - gamma))))) hae
  change
    integral mu (fun sample =>
        (Finset.range horizon).sum (fun t =>
          sampledTrajectoryPureObservedLossAt arms eta gamma t sample) -
        (Finset.range horizon).sum (fun t =>
          observedImportanceWeightedLossAt
            arms eta gamma t sample comparator)) <=
      integral mu (fun sample => Real.log arms.card / eta +
        (eta * (1 / (1 - gamma))) *
          (Finset.range horizon).sum (fun t =>
            observedMixedSquaredImportanceWeightedLossAt
              arms eta gamma t sample)) at hmono
  rw [integral_sub hpureSum hcompSum] at hmono
  rw [integral_add (integrable_const _)
    (hsecondSum.const_mul (eta * (1 / (1 - gamma))))] at hmono
  simpa [mu, MeasureTheory.integral_const_mul] using hmono

/-- Expected exploration-mixed predictable loss is at most expected pure
predictable loss plus `gamma` per round. -/
theorem sampledPredictable_integral_exploredLoss_le_pure_add_gamma
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_lt_one.le loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)) <=
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss t sample)) +
        gamma * (horizon : Real) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_lt_one.le loss.environment
  have hexploredSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => sampledTrajectoryExploredPredictableLossAt
        arms eta gamma loss t sample)
      (fun t _ht => integrable_sampledTrajectoryExploredPredictableLossAt
        mu arms harms eta gamma hgamma_nonneg hgamma_lt_one.le loss t)
  have hpureSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPurePredictableLossAt
          arms eta gamma loss t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => sampledTrajectoryPurePredictableLossAt
        arms eta gamma loss t sample)
      (fun t _ht => integrable_sampledTrajectoryPurePredictableLossAt
        mu arms harms eta gamma loss t)
  have hae : ∀ᵐ sample ∂mu,
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) <=
        (Finset.range horizon).sum (fun t =>
          sampledTrajectoryPurePredictableLossAt
            arms eta gamma loss t sample) +
          gamma * (horizon : Real) := by
    filter_upwards [] with sample
    simpa [sampledTrajectoryExploredPredictableLossAt,
      sampledTrajectoryPurePredictableLossAt] using
      (sampledTrajectory_finiteHorizon_explorationBias_secondMoment
        arms harms eta gamma hgamma_nonneg hgamma_lt_one loss horizon sample).1
  have hmono := integral_mono_ae hexploredSum
    (hpureSum.add (integrable_const _)) hae
  change
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)) <=
      integral mu (fun sample =>
        (Finset.range horizon).sum (fun t =>
          sampledTrajectoryPurePredictableLossAt
            arms eta gamma loss t sample) +
        gamma * (horizon : Real)) at hmono
  rw [integral_add hpureSum (integrable_const _)] at hmono
  simpa [mu] using hmono

/-- The explored probability-mixed estimator square has expectation at most
`|arms| * horizon` under predictable `[0,1]` losses. -/
theorem sampledPredictableObserved_finiteHorizon_secondMoment_integral_le_card_mul
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        observedMixedSquaredImportanceWeightedLossAt
          arms eta gamma t sample)) <=
      (arms.card : Real) * (horizon : Real) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  have hmoment := sampledPredictableObserved_finiteHorizon_first_second_moment
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
      (Classical.choose harms) (Classical.choose_spec harms)
  dsimp only at hmoment
  have htrueSum : Integrable (fun sample => (Finset.range horizon).sum (fun t =>
      arms.sum (fun action =>
        (predictableLossAt loss t sample action) ^ 2))) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => arms.sum (fun action =>
        (predictableLossAt loss t sample action) ^ 2))
      (fun t _ht => integrable_predictableLossSqSumAt mu arms loss t)
  have hae : ∀ᵐ sample ∂mu,
      (Finset.range horizon).sum (fun t => arms.sum (fun action =>
          (predictableLossAt loss t sample action) ^ 2)) <=
        (arms.card : Real) * (horizon : Real) := by
    filter_upwards [] with sample
    calc
      (Finset.range horizon).sum (fun t => arms.sum (fun action =>
          (predictableLossAt loss t sample action) ^ 2)) <=
        (Finset.range horizon).sum (fun _t => (arms.card : Real)) := by
          apply Finset.sum_le_sum
          intro t _ht
          calc
            arms.sum (fun action =>
                (predictableLossAt loss t sample action) ^ 2) <=
              arms.sum (fun _action => (1 : Real)) := by
                apply Finset.sum_le_sum
                intro action _haction
                have hloss : predictableLossAt loss t sample action ∈
                    Set.Icc (0 : Real) 1 := by
                  cases t with
                  | zero => exact loss.initial_mem_unitInterval sample.1 action
                  | succ n =>
                      exact loss.successor_mem_unitInterval n sample.1
                        (Preorder.frestrictLe n sample.2) action
                nlinarith [hloss.1, hloss.2]
            _ = arms.card := by simp
      _ = (arms.card : Real) * (horizon : Real) := by simp [mul_comm]
  have hmono := integral_mono_ae htrueSum (integrable_const _) hae
  calc
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        observedMixedSquaredImportanceWeightedLossAt
          arms eta gamma t sample)) =
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        arms.sum (fun action =>
          (predictableLossAt loss t sample action) ^ 2))) := hmoment.2
    _ <= (arms.card : Real) * (horizon : Real) := by
      simpa [mu] using hmono

/-- Unoptimized expected predictable EXP3 regret bound.  This is the first
complete generated-trajectory theorem on the route; eta/gamma optimization is
kept as a separate deterministic parameter leaf. -/
theorem sampledPredictable_expectedRegret_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    integral mu (fun sample =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) <=
      Real.log arms.card / eta +
        (eta * (1 / (1 - gamma))) *
          ((arms.card : Real) * (horizon : Real)) +
        gamma * (horizon : Real) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  have hexploration := sampledPredictable_integral_exploredLoss_le_pure_add_gamma
    prior arms harms eta gamma hgamma_pos.le hgamma_lt_one loss horizon
  have hpureMoment := sampledPredictablePureObserved_finiteHorizon_integral_eq
    prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
  have hhedge := sampledPredictable_integral_pureHedge_le_exploredSecondMoment
    prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss horizon
      comparator hcomparator
  have hmoment := sampledPredictableObserved_finiteHorizon_first_second_moment
    prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
      comparator hcomparator
  have hsecond :=
    sampledPredictableObserved_finiteHorizon_secondMoment_integral_le_card_mul
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
  dsimp only at hexploration hpureMoment hhedge hmoment hsecond
  have hcoeff_nonneg : 0 <= eta * (1 / (1 - gamma)) := by
    exact mul_nonneg heta.le
      (one_div_nonneg.mpr (sub_nonneg.mpr hgamma_lt_one.le))
  have hscaledSecond := mul_le_mul_of_nonneg_left hsecond hcoeff_nonneg
  have hexploredSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => sampledTrajectoryExploredPredictableLossAt
        arms eta gamma loss t sample)
      (fun t _ht => integrable_sampledTrajectoryExploredPredictableLossAt
        mu arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss t)
  have hcomparatorSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => predictableLossAt loss t sample comparator)
      (fun t _ht => integrable_predictableLossAt mu loss t comparator)
  rw [integral_sub hexploredSum hcomparatorSum]
  nlinarith

end Exp3
end BanditRLProof
