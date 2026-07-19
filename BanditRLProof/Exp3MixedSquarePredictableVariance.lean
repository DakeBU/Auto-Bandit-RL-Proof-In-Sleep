import BanditRLProof.Exp3MixedSquareBernstein
import Mathlib.Probability.Process.Predictable

/-!
# Predictable variance process for mixed-square EXP3 concentration

This module promotes the exact finite-action centered second moment used by
the fixed-tilt Bernstein proof to an explicit generated predictable process.
It supplies the variance-process input needed by a future local Freedman
iteration without claiming that such a tail theorem already exists in Mathlib.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Exact centered second moment of the mixed importance-weighted square under
a finite sampling distribution. -/
noncomputable def mixedSquaredEstimatorCenteredSecondMoment
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (history : History) : Real :=
  arms.sum (fun chosen =>
    prob history chosen *
      (mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
          chosen -
        arms.sum (fun action => (loss history action) ^ 2)) ^ 2)

theorem measurable_mixedSquaredEstimatorCenteredSecondMoment
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Measurable (mixedSquaredEstimatorCenteredSecondMoment arms prob loss) := by
  let mean := fun history : History =>
    arms.sum (fun action => (loss history action) ^ 2)
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun action haction => ?_
    exact (regularity.measurable_loss action haction).pow_const 2
  have hrawPair := measurable_mixedSquaredImportanceWeightedLoss_score
    arms prob loss source epsilon regularity
  refine Finset.measurable_sum arms fun chosen hchosen => ?_
  have hraw : Measurable (fun history =>
      mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
        chosen) :=
    hrawPair.comp (measurable_id.prodMk measurable_const)
  simpa [mixedSquaredEstimatorCenteredSecondMoment, mean] using
    (source.measurable_prob chosen hchosen).mul
      ((hraw.sub hmean).pow_const 2)

theorem mixedSquaredEstimatorCenteredSecondMoment_nonneg
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history)) :
    0 <= mixedSquaredEstimatorCenteredSecondMoment arms prob loss history := by
  unfold mixedSquaredEstimatorCenteredSecondMoment
  exact Finset.sum_nonneg fun chosen hchosen =>
    mul_nonneg (hdist.nonneg chosen hchosen)
      (sq_nonneg _)

theorem mixedSquaredEstimatorCenteredSecondMoment_le_card_div_floor
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    mixedSquaredEstimatorCenteredSecondMoment arms prob loss history <=
      (arms.card : Real) / epsilon := by
  simpa [mixedSquaredEstimatorCenteredSecondMoment] using
    sum_prob_mul_sq_mixedSquaredEstimatorDeviation_le_card_div_floor
      arms (prob history) (loss history) hdist
        epsilon regularity.epsilon_pos (regularity.prob_floor history)
        (regularity.loss_mem_Icc history)

theorem integral_sq_mixedSquaredEstimatorDeviation_finiteActionMeasure_eq
    {History : Type u} {Action : Type v}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history)) :
    integral (finiteActionMeasure arms (prob history)) (fun chosen =>
        (mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
            chosen -
          arms.sum (fun action => (loss history action) ^ 2)) ^ 2) =
      mixedSquaredEstimatorCenteredSecondMoment arms prob loss history := by
  simpa [mixedSquaredEstimatorCenteredSecondMoment] using
    (integral_finiteActionMeasure_eq_sum arms (prob history) hdist
      (fun chosen =>
        (mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
            chosen -
          arms.sum (fun action => (loss history action) ^ 2)) ^ 2))

/-- Transport the centered mixed-square score law from an identified finite
conditional action distribution into the ambient conditional-expectation
kernel. -/
theorem mixedSquaredEstimatorDeviation_condExpKernel_map_eq_finiteActionMeasure_of_condDistrib
    {Omega : Type u} {History : Type v} {Action : Type*}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [mHistory : MeasurableSpace History] [StandardBorelSpace History]
    [mAction : MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source) :
    Filter.Eventually
      (fun omega =>
        Measure.map
            (fun y =>
              mixedSquaredImportanceWeightedLoss arms (prob (history y))
                  (loss (history y)) (action y) -
                arms.sum (fun candidate => (loss (history y) candidate) ^ 2))
            (@condExpKernel Omega mOmega _ mu _ (mHistory.comap history) omega) =
          Measure.map
            (fun selected =>
              mixedSquaredImportanceWeightedLoss arms (prob (history omega))
                  (loss (history omega)) selected -
                arms.sum (fun candidate =>
                  (loss (history omega) candidate) ^ 2))
            (finiteActionMeasure arms (prob (history omega))))
      (ae (mu.trim hhistory.comap_le)) := by
  let mcond := mHistory.comap history
  let mean := fun h : History =>
    arms.sum (fun candidate => (loss h candidate) ^ 2)
  let X := fun omega =>
    mixedSquaredImportanceWeightedLoss arms (prob (history omega))
        (loss (history omega)) (action omega) - mean (history omega)
  let target : Omega -> Measure Real := fun omega => Measure.map
    (fun selected =>
      mixedSquaredImportanceWeightedLoss arms (prob (history omega))
          (loss (history omega)) selected - mean (history omega))
    (finiteActionMeasure arms (prob (history omega)))
  have hmcond : mcond <= mOmega := hhistory.comap_le
  have hrawPair := measurable_mixedSquaredImportanceWeightedLoss_score
    arms prob loss source epsilon regularity
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun candidate hcandidate => ?_
    exact (regularity.measurable_loss candidate hcandidate).pow_const 2
  have haction_map :=
    condExpKernel_map_eq_finiteActionMeasure_of_condDistrib_ae_eq
      (mOmega := mOmega) (mCondition := mHistory) (mAction := mAction)
      mu action history haction hhistory arms prob source hcond
  have hhistory_mcond :
      @Measurable Omega History mcond mHistory history :=
    Measurable.of_comap_le le_rfl
  have hhistory_map :=
    ConditionalExpectationReward.condExpKernel_map_eq_dirac_of_measurable
      (mOmega := mOmega) (mTarget := mHistory)
      mu mcond hmcond history hhistory_mcond
  have hhistory_ae :
      Filter.Eventually
        (fun omega => Filter.EventuallyEq
          (ae (@condExpKernel Omega mOmega _ mu _ mcond omega))
          history (fun _ => history omega))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_map] with omega hmap
    exact ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac
      (mOmega := mOmega) (mTarget := mHistory)
      (@condExpKernel Omega mOmega _ mu _ mcond omega)
      history (history omega) hhistory hmap
  have hkernel_X_eq :
      Filter.Eventually
        (fun omega => Filter.EventuallyEq
          (ae (@condExpKernel Omega mOmega _ mu _ mcond omega))
          X
          (fun y =>
            mixedSquaredImportanceWeightedLoss arms (prob (history omega))
                (loss (history omega)) (action y) - mean (history omega)))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_ae] with omega hfreeze
    filter_upwards [hfreeze] with y hy
    simp only [X]
    rw [hy]
  have hkernel_map :
      Filter.Eventually
        (fun omega =>
          @Measure.map Omega Real mOmega inferInstance X
              (@condExpKernel Omega mOmega _ mu _ mcond omega) =
            target omega)
        (ae (mu.trim hmcond)) := by
    filter_upwards [haction_map, hkernel_X_eq] with omega haction_eq hXeq
    let score : Action -> Real := fun selected =>
      mixedSquaredImportanceWeightedLoss arms (prob (history omega))
          (loss (history omega)) selected - mean (history omega)
    have hscore : Measurable score :=
      (hrawPair.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    calc
      @Measure.map Omega Real mOmega inferInstance X
          (@condExpKernel Omega mOmega _ mu _ mcond omega) =
        @Measure.map Omega Real mOmega inferInstance
          (fun y => score (action y))
          (@condExpKernel Omega mOmega _ mu _ mcond omega) :=
            Measure.map_congr hXeq
      _ = Measure.map score
          (@Measure.map Omega Action mOmega mAction action
            (@condExpKernel Omega mOmega _ mu _ mcond omega)) := by
              rw [Measure.map_map hscore haction]
              congr 1
      _ = target omega := by rw [haction_eq]
  simpa [mcond, mean, X, target] using hkernel_map

/-- The ambient conditional-expectation kernel integrates the squared centered
mixed-square increment to the explicit finite-law centered second moment. -/
theorem integral_sq_mixedSquaredEstimatorDeviation_condExpKernel_eq_of_condDistrib
    {Omega : Type u} {History : Type v} {Action : Type*}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [mHistory : MeasurableSpace History] [StandardBorelSpace History]
    [mAction : MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source) :
    Filter.Eventually
      (fun omega =>
        integral
            (@condExpKernel Omega mOmega _ mu _ (mHistory.comap history) omega)
            (fun y =>
              (mixedSquaredImportanceWeightedLoss arms (prob (history y))
                  (loss (history y)) (action y) -
                arms.sum (fun candidate =>
                  (loss (history y) candidate) ^ 2)) ^ 2) =
          mixedSquaredEstimatorCenteredSecondMoment
            arms prob loss (history omega))
      (ae (mu.trim hhistory.comap_le)) := by
  let mean := fun h : History =>
    arms.sum (fun candidate => (loss h candidate) ^ 2)
  let X := fun omega =>
    mixedSquaredImportanceWeightedLoss arms (prob (history omega))
        (loss (history omega)) (action omega) - mean (history omega)
  have hrawPair := measurable_mixedSquaredImportanceWeightedLoss_score
    arms prob loss source epsilon regularity
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun candidate hcandidate => ?_
    exact (regularity.measurable_loss candidate hcandidate).pow_const 2
  have hX : Measurable X :=
    (hrawPair.comp (hhistory.prodMk haction)).sub (hmean.comp hhistory)
  have hmap :=
    mixedSquaredEstimatorDeviation_condExpKernel_map_eq_finiteActionMeasure_of_condDistrib
      (mOmega := mOmega) (mHistory := mHistory) (mAction := mAction)
      mu history hhistory action haction arms prob loss source epsilon regularity hcond
  filter_upwards [hmap] with omega hmap_omega
  let score : Action -> Real := fun selected =>
    mixedSquaredImportanceWeightedLoss arms (prob (history omega))
        (loss (history omega)) selected - mean (history omega)
  have hscore : Measurable score :=
    (hrawPair.comp (measurable_const.prodMk measurable_id)).sub measurable_const
  calc
    integral
        (@condExpKernel Omega mOmega _ mu _ (mHistory.comap history) omega)
        (fun y =>
          (mixedSquaredImportanceWeightedLoss arms (prob (history y))
              (loss (history y)) (action y) -
            arms.sum (fun candidate => (loss (history y) candidate) ^ 2)) ^ 2) =
      integral
        (Measure.map X
          (@condExpKernel Omega mOmega _ mu _ (mHistory.comap history) omega))
        (fun z : Real => z ^ 2) := by
          simpa [X, mean] using
            (integral_map
              (μ := @condExpKernel Omega mOmega _ mu _
                (mHistory.comap history) omega)
              hX.aemeasurable
              ((measurable_id.pow_const 2).aestronglyMeasurable)).symm
    _ = integral
        (Measure.map score (finiteActionMeasure arms (prob (history omega))))
        (fun z : Real => z ^ 2) := by rw [hmap_omega]
    _ = integral (finiteActionMeasure arms (prob (history omega)))
        (fun selected => score selected ^ 2) := by
          exact integral_map hscore.aemeasurable
            ((measurable_id.pow_const 2).aestronglyMeasurable)
    _ = mixedSquaredEstimatorCenteredSecondMoment
        arms prob loss (history omega) := by
          simpa [score, mean] using
            (integral_sq_mixedSquaredEstimatorDeviation_finiteActionMeasure_eq
              arms prob loss (history omega) (source.distribution (history omega)))

/-- Exact finite-law predictable variance at an actual generated time. -/
noncomputable def sampledTrajectoryPredictableMixedSquaredVarianceAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Env × ((k : Nat) -> Action × Real) -> Real :=
  mixedSquaredEstimatorCenteredSecondMoment arms
    (sampledTrajectoryProbabilityAt arms eta gamma t)
    (predictableLossAt loss t)

theorem measurable_sampledTrajectoryPredictableMixedSquaredVarianceAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable (sampledTrajectoryPredictableMixedSquaredVarianceAt
      arms eta gamma loss t) := by
  exact measurable_mixedSquaredEstimatorCenteredSecondMoment arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t)
    (sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_pos.le hgamma_le_one t)
    (gamma / (arms.card : Real))
    (sampledPredictableTrajectoryLossRegularityAt arms harms eta gamma
      hgamma_pos hgamma_le_one loss t)

theorem sampledTrajectoryPredictableMixedSquaredVarianceAt_nonneg
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    0 <= sampledTrajectoryPredictableMixedSquaredVarianceAt
      arms eta gamma loss t sample := by
  exact mixedSquaredEstimatorCenteredSecondMoment_nonneg arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t) sample
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_nonneg hgamma_le_one t).distribution sample)

theorem sampledTrajectoryPredictableMixedSquaredVarianceAt_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss t sample <=
      (arms.card : Real) / (gamma / (arms.card : Real)) := by
  exact mixedSquaredEstimatorCenteredSecondMoment_le_card_div_floor arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t) sample
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_pos.le hgamma_le_one t).distribution sample)
    (gamma / (arms.card : Real))
    (sampledPredictableTrajectoryLossRegularityAt arms harms eta gamma
      hgamma_pos hgamma_le_one loss t)

/-- At generated time zero, the ambient conditional-expectation kernel given
the environment integrates the squared centered mixed-square increment to the
explicit predictable variance. -/
theorem sampledPredictableMixedSquaredDeviation_zero_condExpKernel_integral_sq_eq_variance
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Filter.Eventually
      (fun omega =>
        integral
            (@condExpKernel
              (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _
              ((inferInstance : MeasurableSpace Env).comap
                (fun sample => sample.1)) omega)
            (fun y =>
              (sampledTrajectoryPredictableMixedSquaredDeviationAt
                arms eta gamma loss 0 y) ^ 2) =
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss 0 omega)
      (ae (mu.trim measurable_fst.comap_le)) := by
  dsimp only
  let algorithm := sampledImportanceWeightedHistoryAlgorithm arms harms
    eta gamma hgamma_pos.le hgamma_le_one
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let prob := fun _env : Env => initialExploredDistribution arms eta gamma
  let source := sampledInitialEnvironmentDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
  let regularity := sampledPredictableInitialLossRegularity
    arms harms eta gamma hgamma_pos hgamma_le_one loss
  have hkernel : Kernel.const Env algorithm.initialAction =
      finiteActionKernel arms prob source := by
    ext env event hevent
    rw [Kernel.const_apply, finiteActionKernel_apply]
    rfl
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source := by
    have hbase :=
      canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
        prior algorithm loss.environment
    rw [hkernel] at hbase
    simpa [mu, algorithm, history, action,
      sampledImportanceWeightedTrajectoryKernel] using hbase
  have hvariance :=
    integral_sq_mixedSquaredEstimatorDeviation_condExpKernel_eq_of_condDistrib
      mu history measurable_fst action (by fun_prop) arms prob loss.initial
        source (gamma / (arms.card : Real)) regularity hcond
  simpa [mu, history, action, prob,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryPredictableMixedSquaredVarianceAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hvariance

/-- At a generated successor time, the ambient conditional-expectation kernel
given the environment and preceding finite prefix integrates the squared
centered mixed-square increment to the explicit predictable variance. -/
theorem sampledPredictableMixedSquaredDeviation_succ_condExpKernel_integral_sq_eq_variance
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    Filter.Eventually
      (fun omega =>
        integral
            (@condExpKernel
              (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _
              ((inferInstance : MeasurableSpace
                (Env × History.FinitePairHistory Action Real n)).comap history)
              omega)
            (fun y =>
              (sampledTrajectoryPredictableMixedSquaredDeviationAt
                arms eta gamma loss (n + 1) y) ^ 2) =
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss (n + 1) omega)
      (ae (mu.trim
        (measurable_fst.prodMk
          ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le)) := by
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
  let source := sampledEnvironmentHistoryDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
  let regularity := sampledPredictableSuccessorLossRegularity
    arms harms eta gamma hgamma_pos hgamma_le_one loss n
  have hhistory : Measurable history := measurable_fst.prodMk
    ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action := by fun_prop
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source := by
    simpa [mu, history, action, prob, source] using
      (sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss n)
  have hvariance :=
    integral_sq_mixedSquaredEstimatorDeviation_condExpKernel_eq_of_condDistrib
      mu history hhistory action haction arms prob roundLoss source
        (gamma / (arms.card : Real)) regularity hcond
  simpa [mu, history, action, prob, roundLoss,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryPredictableMixedSquaredVarianceAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hvariance

/-- Shift the actual-time conditional variances by one. The resulting process
is predictable for the generated deviation filtration. -/
noncomputable def sampledPredictableMixedSquaredVarianceProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Real := fun
  | 0, _sample => 0
  | i + 1, sample =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample


/-- Every shifted mixed-square increment has conditional square integral equal
to the matching shifted predictable variance under the existing generated
filtration. -/
theorem sampledPredictableMixedSquaredDeviationProcess_condExpKernel_integral_sq_eq_varianceProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Filter.Eventually
      (fun omega =>
        integral
            (@condExpKernel
              (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _
              (sampledPredictableDeviationFiltration Env Action n) omega)
            (fun y =>
              (sampledPredictableMixedSquaredDeviationProcess
                arms eta gamma loss (n + 1) y) ^ 2) =
          sampledPredictableMixedSquaredVarianceProcess
            arms eta gamma loss (n + 1) omega)
      (ae (mu.trim
        ((sampledPredictableDeviationFiltration Env Action).le n))) := by
  dsimp only
  cases n with
  | zero =>
      have hzero :=
        sampledPredictableMixedSquaredDeviation_zero_condExpKernel_integral_sq_eq_variance
          prior arms harms eta gamma hgamma_pos hgamma_le_one loss
      dsimp only at hzero
      simpa [sampledPredictableDeviationFiltration_zero,
        sampledPredictableMixedSquaredDeviationProcess,
        sampledPredictableMixedSquaredVarianceProcess] using hzero
  | succ n =>
      have hsucc :=
        sampledPredictableMixedSquaredDeviation_succ_condExpKernel_integral_sq_eq_variance
          prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
      dsimp only at hsucc
      simpa [sampledPredictableDeviationFiltration_succ,
        sampledPredictableMixedSquaredDeviationProcess,
        sampledPredictableMixedSquaredVarianceProcess] using hsucc

theorem measurable_sampledTrajectoryPredictableMixedSquaredVarianceAt_filtration
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable[sampledPredictableDeviationFiltration Env Action t]
      (sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss t) := by
  cases t with
  | zero =>
      let prob := fun _env : Env => initialExploredDistribution arms eta gamma
      let roundLoss := loss.initial
      let variance := mixedSquaredEstimatorCenteredSecondMoment arms prob roundLoss
      let source := sampledInitialEnvironmentDistributionSource
        (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
      let regularity := sampledPredictableInitialLossRegularity
        arms harms eta gamma hgamma_pos hgamma_le_one loss
      have hvariance : Measurable variance :=
        measurable_mixedSquaredEstimatorCenteredSecondMoment arms prob roundLoss
          source (gamma / (arms.card : Real)) regularity
      have hfst : @Measurable
          (Env × ((k : Nat) -> Action × Real)) Env
          (sampledPredictableDeviationFiltration Env Action 0)
          inferInstance Prod.fst := by
        rw [sampledPredictableDeviationFiltration_zero]
        exact Measurable.of_comap_le le_rfl
      simpa [sampledTrajectoryPredictableMixedSquaredVarianceAt,
        mixedSquaredEstimatorCenteredSecondMoment, sampledTrajectoryProbabilityAt,
        predictableLossAt, variance, prob, roundLoss] using
        hvariance.comp hfst
  | succ n =>
      let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.1, Preorder.frestrictLe n sample.2)
      let prob := fun input : Env × History.FinitePairHistory Action Real n =>
        sampledHistoryDistribution arms eta gamma n input.2
      let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
        loss.successor n input.1 input.2
      let variance := mixedSquaredEstimatorCenteredSecondMoment arms prob roundLoss
      let source := sampledEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
      let regularity := sampledPredictableSuccessorLossRegularity
        arms harms eta gamma hgamma_pos hgamma_le_one loss n
      have hvariance : Measurable variance :=
        measurable_mixedSquaredEstimatorCenteredSecondMoment arms prob roundLoss
          source (gamma / (arms.card : Real)) regularity
      have hhistory : @Measurable
          (Env × ((k : Nat) -> Action × Real))
          (Env × History.FinitePairHistory Action Real n)
          (sampledPredictableDeviationFiltration Env Action (n + 1))
          inferInstance history := by
        rw [sampledPredictableDeviationFiltration_succ]
        exact Measurable.of_comap_le le_rfl
      simpa [sampledTrajectoryPredictableMixedSquaredVarianceAt,
        mixedSquaredEstimatorCenteredSecondMoment, sampledTrajectoryProbabilityAt,
        predictableLossAt, variance, prob, roundLoss, history] using
        hvariance.comp hhistory

theorem sampledPredictableMixedSquaredVarianceProcess_isPredictable
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    IsPredictable (sampledPredictableDeviationFiltration Env Action)
      (sampledPredictableMixedSquaredVarianceProcess arms eta gamma loss) := by
  apply isPredictable_of_measurable_add_one
  · change Measurable[sampledPredictableDeviationFiltration Env Action 0]
      (fun _ : Env × ((k : Nat) -> Action × Real) => (0 : Real))
    exact measurable_const
  · intro n
    simpa [sampledPredictableMixedSquaredVarianceProcess] using
      measurable_sampledTrajectoryPredictableMixedSquaredVarianceAt_filtration
        arms harms eta gamma hgamma_pos hgamma_le_one loss n

theorem sampledPredictableMixedSquaredVarianceProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPredictableMixedSquaredVarianceProcess
          arms eta gamma loss i sample) =
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample) := by
  induction horizon with
  | zero => simp [sampledPredictableMixedSquaredVarianceProcess]
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by rfl,
        Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      rfl

theorem sampledPredictableMixedSquaredVariance_sum_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample) <=
      (horizon : Real) *
        ((arms.card : Real) / (gamma / (arms.card : Real))) := by
  calc
    (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample) <=
      (Finset.range horizon).sum (fun _i =>
        (arms.card : Real) / (gamma / (arms.card : Real))) := by
          exact Finset.sum_le_sum fun i _hi =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt_le
              arms harms eta gamma hgamma_pos hgamma_le_one loss i sample
    _ = (horizon : Real) *
        ((arms.card : Real) / (gamma / (arms.card : Real))) := by simp

end BanditRLProof.Exp3
