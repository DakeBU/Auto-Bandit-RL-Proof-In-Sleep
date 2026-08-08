import BanditRLProof.Exp3ExpectedRegret

/-!
# Realized predictable EXP3 regret

This module transports the compiled predictable `p_t`-mixed expected-regret
bound to the scalar loss actually observed on the generated trajectory.  The
only probabilistic step is the existing conditional action law: conditionally
on the pre-action history, the sampled action has finite distribution `p_t`.
-/

namespace BanditRLProof
namespace Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The scalar loss realized at an actual generated-trajectory time. -/
def sampledTrajectoryRealizedLossAt
    {Env : Type u} {Action : Type v}
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (sample.2 t).2

/-- Generated predictable feedback identifies the realized scalar loss with
the predictable coordinate selected by the sampled action. -/
theorem sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
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
    sampledTrajectoryRealizedLossAt t =ᵐ[mu]
      (fun sample => predictableLossAt loss t sample (sample.2 t).1) := by
  dsimp only
  cases t with
  | zero =>
      simpa [sampledTrajectoryRealizedLossAt, predictableLossAt,
        sampledImportanceWeightedTrajectoryKernel] using
        (canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
          prior
            (sampledImportanceWeightedHistoryAlgorithm arms harms eta gamma
              hgamma_nonneg hgamma_le_one)
            loss)
  | succ n =>
      simpa [sampledTrajectoryRealizedLossAt, predictableLossAt] using
        (sampledPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
          prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)

/-- The selected predictable coordinate is measurable on the full trajectory
space, even though the coordinate itself varies with the sampled action. -/
theorem measurable_sampledTrajectorySelectedPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Real) =>
      predictableLossAt loss t sample (sample.2 t).1) := by
  cases t with
  | zero =>
      exact loss.measurable_initial.comp
        (measurable_fst.prodMk
          (measurable_fst.comp
            ((measurable_pi_apply 0).comp measurable_snd)))
  | succ n =>
      have haction : Measurable
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.2 (n + 1)).1) := by
        fun_prop
      exact (loss.measurable_successor n).comp
        (measurable_fst.prodMk
          (((Preorder.measurable_frestrictLe n).comp measurable_snd).prodMk
            haction))

theorem sampledTrajectorySelectedPredictableLossAt_mem_unitInterval
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    predictableLossAt loss t sample (sample.2 t).1 ∈ Set.Icc (0 : Real) 1 := by
  cases t with
  | zero =>
      exact loss.initial_mem_unitInterval sample.1 (sample.2 0).1
  | succ n =>
      exact loss.successor_mem_unitInterval n sample.1
        (Preorder.frestrictLe n sample.2) (sample.2 (n + 1)).1

theorem integrable_sampledTrajectorySelectedPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Integrable (fun sample =>
      predictableLossAt loss t sample (sample.2 t).1) mu := by
  refine Integrable.of_bound
    (measurable_sampledTrajectorySelectedPredictableLossAt loss t).aestronglyMeasurable
    1 ?_
  exact Filter.Eventually.of_forall fun sample => by
    have hmem := sampledTrajectorySelectedPredictableLossAt_mem_unitInterval
      loss t sample
    simpa [Real.norm_eq_abs, abs_of_nonneg hmem.1] using hmem.2

theorem integrable_sampledTrajectoryRealizedLossAt
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
    Integrable (sampledTrajectoryRealizedLossAt t) mu := by
  dsimp only
  exact (integrable_sampledTrajectorySelectedPredictableLossAt
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms eta gamma
      hgamma_nonneg hgamma_le_one loss.environment) loss t).congr
        (sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
          prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss t).symm

/-- At time zero, the expected realized loss is the exploration-distribution
mixed predictable loss. -/
theorem sampledPredictableRealizedInitial_integral_eq_explored
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    integral mu (sampledTrajectoryRealizedLossAt 0) =
      integral mu
        (sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss 0) := by
  dsimp only
  let algorithm := sampledImportanceWeightedHistoryAlgorithm arms harms
    eta gamma hgamma_nonneg hgamma_le_one
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let prob := fun _env : Env => initialExploredDistribution arms eta gamma
  let source := sampledInitialEnvironmentDistributionSource
    (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one
  let policy := finiteActionKernel arms prob source
  let score := fun z : Env × Action => loss.initial z.1 z.2
  have hhistory : Measurable history := by fun_prop
  have haction : Measurable action := by fun_prop
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
  have hscore : Measurable score := loss.measurable_initial
  have hintegrable : Integrable score (mu.map history ⊗ₘ policy) := by
    refine Integrable.of_bound hscore.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun z => by
      have hmem := loss.initial_mem_unitInterval z.1 z.2
      simpa [score, Real.norm_eq_abs, abs_of_nonneg hmem.1] using hmem.2
  have hvector :=
    integral_historyAction_eq_integral_sum_of_condDistrib_ae_eq_finiteActionMeasure
      mu history hhistory action haction arms prob
      (fun env => source.distribution env) policy hpolicy hcond score hscore
      hintegrable
  have hreward :=
    sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss 0
  dsimp only at hreward
  have hmix : Measurable (fun env =>
      arms.sum (fun selected => prob env selected * loss.initial env selected)) := by
    refine Finset.measurable_sum arms fun selected hselected => ?_
    exact (source.measurable_prob selected hselected).mul
      (loss.measurable_initial.comp
        (measurable_id.prodMk
          (measurable_const : Measurable (fun _ : Env => selected))))
  have hmap := integral_map (μ := mu) hhistory.aemeasurable
    hmix.aestronglyMeasurable
  calc
    integral mu (sampledTrajectoryRealizedLossAt 0) =
        integral mu (fun sample => score (history sample, action sample)) := by
      apply integral_congr_ae
      simpa [score, history, action, predictableLossAt] using hreward
    _ = integral (mu.map history) (fun env =>
        arms.sum (fun selected => prob env selected * score (env, selected))) :=
      hvector
    _ = integral mu
        (sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss 0) := by
      simpa [score, history, prob, sampledTrajectoryExploredPredictableLossAt,
        sampledTrajectoryProbabilityAt] using hmap

/-- At a successor time, conditioning on the retained environment/history
prefix converts the expected selected predictable coordinate to the `p_t`
finite sum. -/
theorem sampledPredictableRealizedSuccessor_integral_eq_explored
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    integral mu (sampledTrajectoryRealizedLossAt (n + 1)) =
      integral mu
        (sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss (n + 1)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 (n + 1)).1
  let prob := fun input : Env × History.FinitePairHistory Action Real n =>
    sampledHistoryDistribution arms eta gamma n input.2
  let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
    loss.successor n input.1 input.2
  let localSource := exploredHistoryDistributionSource arms harms eta gamma
    (sampledHistoryScore arms eta gamma)
    (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma)
    hgamma_nonneg hgamma_le_one n
  let source := sampledEnvironmentHistoryDistributionSource
    (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one n
  let policy : Kernel
      (Env × History.FinitePairHistory Action Real n) Action :=
    (finiteActionKernel arms
      (sampledHistoryDistribution arms eta gamma n) localSource).comap
        (fun input : Env × History.FinitePairHistory Action Real n => input.2)
        measurable_snd
  let score := fun z :
      (Env × History.FinitePairHistory Action Real n) × Action =>
    roundLoss z.1 z.2
  have hhistory : Measurable history :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action := by fun_prop
  have hpolicyEq : policy = finiteActionKernel arms prob source := by
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
        prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)
  have hscore : Measurable score := by
    exact (loss.measurable_successor n).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hintegrable : Integrable score (mu.map history ⊗ₘ policy) := by
    refine Integrable.of_bound hscore.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun z => by
      have hmem := loss.successor_mem_unitInterval n z.1.1 z.1.2 z.2
      simpa [score, roundLoss, Real.norm_eq_abs, abs_of_nonneg hmem.1] using hmem.2
  have hvector :=
    integral_historyAction_eq_integral_sum_of_condDistrib_ae_eq_finiteActionMeasure
      mu history hhistory action haction arms prob
      (fun input => source.distribution input) policy hpolicy hcond score hscore
      hintegrable
  have hreward :=
    sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss (n + 1)
  dsimp only at hreward
  have hmix : Measurable (fun input =>
      arms.sum (fun selected => prob input selected * roundLoss input selected)) := by
    refine Finset.measurable_sum arms fun selected hselected => ?_
    exact (source.measurable_prob selected hselected).mul
      ((loss.measurable_successor n).comp
        (measurable_fst.prodMk
          (measurable_snd.prodMk
            (measurable_const : Measurable
              (fun _ : Env × History.FinitePairHistory Action Real n => selected)))))
  have hmap := integral_map (μ := mu) hhistory.aemeasurable
    hmix.aestronglyMeasurable
  calc
    integral mu (sampledTrajectoryRealizedLossAt (n + 1)) =
        integral mu (fun sample => score (history sample, action sample)) := by
      apply integral_congr_ae
      simpa [score, roundLoss, history, action, predictableLossAt] using hreward
    _ = integral (mu.map history) (fun input =>
        arms.sum (fun selected => prob input selected * score (input, selected))) :=
      hvector
    _ = integral mu
        (sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss (n + 1)) := by
      simpa [score, roundLoss, history, prob,
        sampledTrajectoryExploredPredictableLossAt,
        sampledTrajectoryProbabilityAt] using hmap

/-- Every actual time has the realized-to-`p_t`-mixed first-moment identity. -/
theorem sampledPredictableRealizedAt_integral_eq_explored
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
    integral mu (sampledTrajectoryRealizedLossAt t) =
      integral mu
        (sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t) := by
  cases t with
  | zero =>
      exact sampledPredictableRealizedInitial_integral_eq_explored
        prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss
  | succ n =>
      exact sampledPredictableRealizedSuccessor_integral_eq_explored
        prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n

/-- The realized and exploration-mixed predictable cumulative losses have the
same expectation over every finite horizon. -/
theorem sampledPredictableRealized_finiteHorizon_integral_eq_explored
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedLossAt t sample)) =
      integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  calc
    integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedLossAt t sample)) =
      (Finset.range horizon).sum (fun t =>
        integral mu (sampledTrajectoryRealizedLossAt t)) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon)
        (fun t sample => sampledTrajectoryRealizedLossAt t sample)
        (fun t _ht => integrable_sampledTrajectoryRealizedLossAt
          prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss t)
    _ = (Finset.range horizon).sum (fun t =>
        integral mu (sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact sampledPredictableRealizedAt_integral_eq_explored
        prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss t
    _ = integral mu (fun sample => (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)) := by
      symm
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon)
        (fun t sample => sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)
        (fun t _ht => integrable_sampledTrajectoryExploredPredictableLossAt
          mu arms harms eta gamma hgamma_nonneg hgamma_le_one loss t)

/-- Unoptimized expected regret for the scalar losses actually realized by the
sampled predictable EXP3 trajectory. -/
theorem sampledPredictable_realizedExpectedRegret_le
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
          sampledTrajectoryRealizedLossAt t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) <=
      Real.log arms.card / eta +
        (eta * (1 / (1 - gamma))) *
          ((arms.card : Real) * (horizon : Real)) +
        gamma * (horizon : Real) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  have htransport :=
    sampledPredictableRealized_finiteHorizon_integral_eq_explored
      prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss horizon
  have hbase := sampledPredictable_expectedRegret_le
    prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss horizon
      comparator hcomparator
  dsimp only at htransport hbase
  have hrealizedSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedLossAt t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => sampledTrajectoryRealizedLossAt t sample)
      (fun t _ht => integrable_sampledTrajectoryRealizedLossAt
        prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss t)
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
  rw [integral_sub hexploredSum hcomparatorSum] at hbase
  rw [integral_sub hrealizedSum hcomparatorSum]
  rw [htransport]
  exact hbase

/-- Tuned large-horizon expected regret for the scalar loss actually realized
by the sampled predictable EXP3 trajectory. -/
theorem sampledPredictable_realizedExpectedRegret_le_four_mul_sqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (hhorizon_pos : 0 < horizon)
    (hscale :
      4 * (arms.card : Real) * Real.log arms.card <= (horizon : Real))
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let K := (arms.card : Real)
    let T := (horizon : Real)
    let mu := prior ⊗ₘ tunedPredictableTrajectoryKernel
      arms harms hcard_two loss horizon hhorizon_pos hscale
    integral mu (fun sample =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryRealizedLossAt t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) <=
      4 * Real.sqrt (K * T * Real.log K) := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon_pos
  have hgamma_pos :=
    tunedExplorationRate_pos (arms.card : Real) (horizon : Real) hK_one hT
  have hgamma_half :=
    tunedExplorationRate_le_half (arms.card : Real) (horizon : Real) hT hscale
  let eta := tunedLearningRate (arms.card : Real) (horizon : Real)
  let gamma := tunedExplorationRate (arms.card : Real) (horizon : Real)
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le (hgamma_half.trans (by norm_num)) loss.environment
  change integral mu (fun sample =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryRealizedLossAt t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) <=
    4 * Real.sqrt
      ((arms.card : Real) * (horizon : Real) * Real.log arms.card)
  have htransport :=
    sampledPredictableRealized_finiteHorizon_integral_eq_explored
      prior arms harms eta gamma hgamma_pos.le
        (hgamma_half.trans (by norm_num)) loss horizon
  have hbase := sampledPredictable_expectedRegret_le_four_mul_sqrt
    prior arms harms hcard_two loss horizon hhorizon_pos hscale comparator
      hcomparator
  dsimp only [tunedPredictableTrajectoryKernel] at hbase
  dsimp only at htransport
  have hrealizedSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedLossAt t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => sampledTrajectoryRealizedLossAt t sample)
      (fun t _ht => integrable_sampledTrajectoryRealizedLossAt
        prior arms harms eta gamma hgamma_pos.le
          (hgamma_half.trans (by norm_num)) loss t)
  have hexploredSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => sampledTrajectoryExploredPredictableLossAt
        arms eta gamma loss t sample)
      (fun t _ht => integrable_sampledTrajectoryExploredPredictableLossAt
        mu arms harms eta gamma hgamma_pos.le
          (hgamma_half.trans (by norm_num)) loss t)
  have hcomparatorSum : Integrable (fun sample =>
      (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator)) mu :=
    IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
      (fun t sample => predictableLossAt loss t sample comparator)
      (fun t _ht => integrable_predictableLossAt mu loss t comparator)
  rw [integral_sub hexploredSum hcomparatorSum] at hbase
  rw [integral_sub hrealizedSum hcomparatorSum]
  rw [htransport]
  exact hbase

end Exp3
end BanditRLProof
