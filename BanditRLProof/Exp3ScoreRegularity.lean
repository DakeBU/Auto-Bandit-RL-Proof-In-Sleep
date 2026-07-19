import BanditRLProof.Exp3ActionProcess

/-!
# Regularity of one-round EXP3 importance-weighted scores

This module discharges the measurable-score and integrability premises of the
generated one-round EXP3 action process.  A uniform positive probability floor
and measurable losses in `[0, 1]` give explicit pointwise bounds for the
armwise, mixed first-moment, and mixed second-moment scores.
-/

namespace BanditRLProof
namespace Exp3

open MeasureTheory

universe u v

/-- Measurable bounded losses and a uniform exploration floor on the finite support. -/
structure BoundedMeasurableLossWithProbabilityFloor
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (epsilon : Real) : Prop where
  epsilon_pos : 0 < epsilon
  prob_floor : forall history action, action ∈ arms ->
    epsilon <= prob history action
  measurable_loss : forall action, action ∈ arms ->
    Measurable (fun history => loss history action)
  loss_mem_Icc : forall history action, action ∈ arms ->
    loss history action ∈ Set.Icc (0 : Real) 1

theorem BoundedMeasurableLossWithProbabilityFloor.prob_pos
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    {arms : Finset Action} {prob loss : History -> Action -> Real}
    {epsilon : Real}
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (history : History) (action : Action) (haction : action ∈ arms) :
    0 < prob history action :=
  regularity.epsilon_pos.trans_le
    (regularity.prob_floor history action haction)

/-- A fixed-arm importance-weighted score is measurable on history/action pairs. -/
theorem measurable_importanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (action : Action) (haction : action ∈ arms) :
    Measurable (fun sample : History × Action =>
      importanceWeightedLoss (prob sample.1) (loss sample.1)
        sample.2 action) := by
  unfold importanceWeightedLoss
  refine Measurable.ite ?_ ?_ measurable_const
  · simpa only [Set.mem_setOf_eq] using
      (measurable_snd (measurableSet_singleton action))
  · exact
      ((regularity.measurable_loss action haction).comp measurable_fst).div
        ((source.measurable_prob action haction).comp measurable_fst)

/-- The probability-mixed first-moment score is measurable. -/
theorem measurable_mixedImportanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Measurable (fun sample : History × Action =>
      mixedImportanceWeightedLoss arms (prob sample.1) (loss sample.1)
        sample.2) := by
  unfold mixedImportanceWeightedLoss
  refine Finset.measurable_sum arms fun action haction => ?_
  exact ((source.measurable_prob action haction).comp measurable_fst).mul
    (measurable_importanceWeightedLoss_score arms prob loss source epsilon
      regularity action haction)

/-- A score mixed by a second measurable finite distribution is measurable. -/
theorem measurable_weightedImportanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (prob weight loss : History -> Action -> Real)
    (probSource : MeasurableFiniteActionDistribution arms prob)
    (weightSource : MeasurableFiniteActionDistribution arms weight)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Measurable (fun sample : History × Action =>
      weightedImportanceWeightedLoss arms (prob sample.1)
        (weight sample.1) (loss sample.1) sample.2) := by
  unfold weightedImportanceWeightedLoss
  refine Finset.measurable_sum arms fun action haction => ?_
  exact ((weightSource.measurable_prob action haction).comp measurable_fst).mul
    (measurable_importanceWeightedLoss_score arms prob loss probSource epsilon
      regularity action haction)

/-- The probability-mixed second-moment score is measurable. -/
theorem measurable_mixedSquaredImportanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Measurable (fun sample : History × Action =>
      mixedSquaredImportanceWeightedLoss arms (prob sample.1)
        (loss sample.1) sample.2) := by
  unfold mixedSquaredImportanceWeightedLoss
  refine Finset.measurable_sum arms fun action haction => ?_
  exact ((source.measurable_prob action haction).comp measurable_fst).mul
    ((measurable_importanceWeightedLoss_score arms prob loss source epsilon
      regularity action haction).pow_const 2)

/-- A fixed-arm importance-weighted score is bounded by the reciprocal floor. -/
theorem norm_importanceWeightedLoss_score_le_inv_floor
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (history : History) (chosen action : Action) (haction : action ∈ arms) :
    ‖importanceWeightedLoss (prob history) (loss history) chosen action‖ <=
      1 / epsilon := by
  have hprob_pos := regularity.prob_pos history action haction
  have hloss := regularity.loss_mem_Icc history action haction
  unfold importanceWeightedLoss
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hloss.1 hprob_pos.le)]
    exact (div_le_div_of_nonneg_right hloss.2 hprob_pos.le).trans
      (one_div_le_one_div_of_le regularity.epsilon_pos
        (regularity.prob_floor history action haction))
  · simpa only [norm_zero] using
      (one_div_pos.mpr regularity.epsilon_pos).le

/-- The mixed first-moment score is bounded by the reciprocal floor. -/
theorem norm_mixedImportanceWeightedLoss_score_le_inv_floor
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (history : History) (chosen : Action) :
    ‖mixedImportanceWeightedLoss arms (prob history) (loss history) chosen‖ <=
      1 / epsilon := by
  rw [Real.norm_eq_abs]
  unfold mixedImportanceWeightedLoss
  calc
    |arms.sum (fun action =>
        prob history action *
          importanceWeightedLoss (prob history) (loss history) chosen action)| <=
        arms.sum (fun action =>
          |prob history action *
            importanceWeightedLoss (prob history) (loss history) chosen action|) :=
      Finset.abs_sum_le_sum_abs _ arms
    _ <= arms.sum (fun action => prob history action * (1 / epsilon)) := by
      apply Finset.sum_le_sum
      intro action haction
      have hprob_nonneg := (source.distribution history).nonneg action haction
      have hiw_bound :=
        norm_importanceWeightedLoss_score_le_inv_floor arms prob loss epsilon
          regularity history chosen action haction
      rw [Real.norm_eq_abs] at hiw_bound
      rw [abs_mul, abs_of_nonneg hprob_nonneg]
      exact mul_le_mul_of_nonneg_left hiw_bound hprob_nonneg
    _ = arms.sum (prob history) * (1 / epsilon) := by
      rw [Finset.sum_mul]
    _ = 1 / epsilon := by
      rw [(source.distribution history).sum_eq_one, one_mul]

/-- Mixing by any finite probability vector preserves the reciprocal-floor
bound for the importance-weighted score. -/
theorem norm_weightedImportanceWeightedLoss_score_le_inv_floor
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [DecidableEq Action]
    (arms : Finset Action) (prob weight loss : History -> Action -> Real)
    (weightSource : MeasurableFiniteActionDistribution arms weight)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (history : History) (chosen : Action) :
    ‖weightedImportanceWeightedLoss arms (prob history) (weight history)
        (loss history) chosen‖ <= 1 / epsilon := by
  rw [Real.norm_eq_abs]
  unfold weightedImportanceWeightedLoss
  calc
    |arms.sum (fun action =>
        weight history action *
          importanceWeightedLoss (prob history) (loss history) chosen action)| <=
        arms.sum (fun action =>
          |weight history action *
            importanceWeightedLoss (prob history) (loss history) chosen action|) :=
      Finset.abs_sum_le_sum_abs _ arms
    _ <= arms.sum (fun action => weight history action * (1 / epsilon)) := by
      apply Finset.sum_le_sum
      intro action haction
      have hweight_nonneg :=
        (weightSource.distribution history).nonneg action haction
      have hiw_bound :=
        norm_importanceWeightedLoss_score_le_inv_floor arms prob loss epsilon
          regularity history chosen action haction
      rw [Real.norm_eq_abs] at hiw_bound
      rw [abs_mul, abs_of_nonneg hweight_nonneg]
      exact mul_le_mul_of_nonneg_left hiw_bound hweight_nonneg
    _ = arms.sum (weight history) * (1 / epsilon) := by
      rw [Finset.sum_mul]
    _ = 1 / epsilon := by
      rw [(weightSource.distribution history).sum_eq_one, one_mul]

/-- The mixed second-moment score is bounded by the square reciprocal floor. -/
theorem norm_mixedSquaredImportanceWeightedLoss_score_le_inv_floor_sq
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (history : History) (chosen : Action) :
    ‖mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
        chosen‖ <= (1 / epsilon) ^ 2 := by
  have hbound_nonneg : 0 <= 1 / epsilon :=
    (one_div_pos.mpr regularity.epsilon_pos).le
  rw [Real.norm_eq_abs]
  unfold mixedSquaredImportanceWeightedLoss
  rw [abs_of_nonneg]
  · calc
      arms.sum (fun action =>
          prob history action *
            (importanceWeightedLoss (prob history) (loss history)
              chosen action) ^ 2) <=
          arms.sum (fun action => prob history action * (1 / epsilon) ^ 2) := by
        apply Finset.sum_le_sum
        intro action haction
        have hprob_nonneg := (source.distribution history).nonneg action haction
        have hiw_nonneg := importanceWeightedLoss_nonneg (chosen := chosen)
          hprob_nonneg (regularity.loss_mem_Icc history action haction).1
        have hiw_le :
            importanceWeightedLoss (prob history) (loss history) chosen action <=
              1 / epsilon := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hiw_nonneg] using
            norm_importanceWeightedLoss_score_le_inv_floor arms prob loss
              epsilon regularity history chosen action haction
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hiw_nonneg hbound_nonneg).2 hiw_le) hprob_nonneg
      _ = arms.sum (prob history) * (1 / epsilon) ^ 2 := by
        rw [Finset.sum_mul]
      _ = (1 / epsilon) ^ 2 := by
        rw [(source.distribution history).sum_eq_one, one_mul]
  · exact Finset.sum_nonneg fun action haction =>
      mul_nonneg ((source.distribution history).nonneg action haction)
        (sq_nonneg _)

/-- The armwise score is integrable under the generated history/action law. -/
theorem integrable_importanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (action : Action) (haction : action ∈ arms) :
    Integrable (fun sample : History × Action =>
      importanceWeightedLoss (prob sample.1) (loss sample.1)
        sample.2 action)
      (Measure.compProd historyMu (finiteActionKernel arms prob source)) := by
  refine Integrable.of_bound
    (measurable_importanceWeightedLoss_score arms prob loss source epsilon
      regularity action haction).aestronglyMeasurable
    (1 / epsilon) ?_
  exact Filter.Eventually.of_forall fun sample =>
    norm_importanceWeightedLoss_score_le_inv_floor arms prob loss epsilon
      regularity sample.1 sample.2 action haction

/-- The mixed first-moment score is integrable under the generated law. -/
theorem integrable_mixedImportanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Integrable (fun sample : History × Action =>
      mixedImportanceWeightedLoss arms (prob sample.1) (loss sample.1)
        sample.2)
      (Measure.compProd historyMu (finiteActionKernel arms prob source)) := by
  refine Integrable.of_bound
    (measurable_mixedImportanceWeightedLoss_score arms prob loss source epsilon
      regularity).aestronglyMeasurable
    (1 / epsilon) ?_
  exact Filter.Eventually.of_forall fun sample =>
    norm_mixedImportanceWeightedLoss_score_le_inv_floor arms prob loss source
      epsilon regularity sample.1 sample.2

/-- A predictably weighted importance-weighted score is integrable under the
sampling law when both finite distributions are measurable. -/
theorem integrable_weightedImportanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob weight loss : History -> Action -> Real)
    (probSource : MeasurableFiniteActionDistribution arms prob)
    (weightSource : MeasurableFiniteActionDistribution arms weight)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Integrable (fun sample : History × Action =>
      weightedImportanceWeightedLoss arms (prob sample.1)
        (weight sample.1) (loss sample.1) sample.2)
      (Measure.compProd historyMu (finiteActionKernel arms prob probSource)) := by
  refine Integrable.of_bound
    (measurable_weightedImportanceWeightedLoss_score arms prob weight loss
      probSource weightSource epsilon regularity).aestronglyMeasurable
    (1 / epsilon) ?_
  exact Filter.Eventually.of_forall fun sample =>
    norm_weightedImportanceWeightedLoss_score_le_inv_floor arms prob weight loss
      weightSource epsilon regularity sample.1 sample.2

/-- The mixed second-moment score is integrable under the generated law. -/
theorem integrable_mixedSquaredImportanceWeightedLoss_score
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Integrable (fun sample : History × Action =>
      mixedSquaredImportanceWeightedLoss arms (prob sample.1)
        (loss sample.1) sample.2)
      (Measure.compProd historyMu (finiteActionKernel arms prob source)) := by
  refine Integrable.of_bound
    (measurable_mixedSquaredImportanceWeightedLoss_score arms prob loss source
      epsilon regularity).aestronglyMeasurable
    ((1 / epsilon) ^ 2) ?_
  exact Filter.Eventually.of_forall fun sample =>
    norm_mixedSquaredImportanceWeightedLoss_score_le_inv_floor_sq arms prob loss
      source epsilon regularity sample.1 sample.2

/-- A bounded armwise score remains integrable when the sampled action is any
measurable function on a finite history measure. -/
theorem integrable_importanceWeightedLoss_selected_of_isFiniteMeasure
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure History) [IsFiniteMeasure mu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (chosen : History -> Action) (hchosen : Measurable chosen)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    Integrable (fun history =>
      importanceWeightedLoss (prob history) (loss history)
        (chosen history) comparator) mu := by
  refine Integrable.of_bound
    ((measurable_importanceWeightedLoss_score arms prob loss source epsilon
      regularity comparator hcomparator).comp
        (measurable_id.prodMk hchosen)).aestronglyMeasurable
    (1 / epsilon) ?_
  exact Filter.Eventually.of_forall fun history =>
    norm_importanceWeightedLoss_score_le_inv_floor arms prob loss epsilon
      regularity history (chosen history) comparator hcomparator

/-- A predictably weighted score remains integrable when the sampled action is
an arbitrary measurable function on a finite measure. -/
theorem integrable_weightedImportanceWeightedLoss_selected_of_isFiniteMeasure
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure History) [IsFiniteMeasure mu]
    (arms : Finset Action) (prob weight loss : History -> Action -> Real)
    (probSource : MeasurableFiniteActionDistribution arms prob)
    (weightSource : MeasurableFiniteActionDistribution arms weight)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (chosen : History -> Action) (hchosen : Measurable chosen) :
    Integrable (fun history =>
      weightedImportanceWeightedLoss arms (prob history) (weight history)
        (loss history) (chosen history)) mu := by
  refine Integrable.of_bound
    ((measurable_weightedImportanceWeightedLoss_score arms prob weight loss
      probSource weightSource epsilon regularity).comp
        (measurable_id.prodMk hchosen)).aestronglyMeasurable
    (1 / epsilon) ?_
  exact Filter.Eventually.of_forall fun history =>
    norm_weightedImportanceWeightedLoss_score_le_inv_floor arms prob weight loss
      weightSource epsilon regularity history (chosen history)

/-- A bounded mixed second-moment score remains integrable when the sampled
action is any measurable function on a finite history measure. -/
theorem integrable_mixedSquaredImportanceWeightedLoss_selected_of_isFiniteMeasure
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure History) [IsFiniteMeasure mu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (chosen : History -> Action) (hchosen : Measurable chosen) :
    Integrable (fun history =>
      mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
        (chosen history)) mu := by
  refine Integrable.of_bound
    ((measurable_mixedSquaredImportanceWeightedLoss_score arms prob loss source
      epsilon regularity).comp
        (measurable_id.prodMk hchosen)).aestronglyMeasurable
    ((1 / epsilon) ^ 2) ?_
  exact Filter.Eventually.of_forall fun history =>
    norm_mixedSquaredImportanceWeightedLoss_score_le_inv_floor_sq arms prob loss
      source epsilon regularity history (chosen history)

/-- Canonical armwise identity with score regularity inferred from bounded losses. -/
theorem actionProcess_integral_importanceWeightedLoss_eq_integral_loss_of_regularity
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    integral (actionProcessMeasure historyMu arms prob source) (fun sample =>
        importanceWeightedLoss (prob (actionProcessHistory sample))
          (loss (actionProcessHistory sample)) (actionProcessAction sample)
          comparator) =
      integral historyMu (fun history => loss history comparator) := by
  exact actionProcess_integral_importanceWeightedLoss_eq_integral_loss
    historyMu arms prob loss source
    (fun history action haction => regularity.prob_pos history action haction)
    comparator hcomparator
    (measurable_importanceWeightedLoss_score arms prob loss source epsilon
      regularity comparator hcomparator)
    (integrable_importanceWeightedLoss_score historyMu arms prob loss source
      epsilon regularity comparator hcomparator)

/-- Canonical mixed first-moment identity with score regularity inferred. -/
theorem actionProcess_integral_mixedImportanceWeightedLoss_eq_integral_mixedLoss_of_regularity
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    integral (actionProcessMeasure historyMu arms prob source) (fun sample =>
        mixedImportanceWeightedLoss arms
          (prob (actionProcessHistory sample))
          (loss (actionProcessHistory sample)) (actionProcessAction sample)) =
      integral historyMu (fun history =>
        arms.sum (fun action => prob history action * loss history action)) := by
  exact actionProcess_integral_mixedImportanceWeightedLoss_eq_integral_mixedLoss
    historyMu arms prob loss source
    (fun history action haction => regularity.prob_pos history action haction)
    (measurable_mixedImportanceWeightedLoss_score arms prob loss source epsilon
      regularity)
    (integrable_mixedImportanceWeightedLoss_score historyMu arms prob loss source
      epsilon regularity)

/-- Canonical mixed second-moment identity with score regularity inferred. -/
theorem actionProcess_integral_mixedSquaredImportanceWeightedLoss_eq_integral_sum_loss_sq_of_regularity
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    integral (actionProcessMeasure historyMu arms prob source) (fun sample =>
        mixedSquaredImportanceWeightedLoss arms
          (prob (actionProcessHistory sample))
          (loss (actionProcessHistory sample)) (actionProcessAction sample)) =
      integral historyMu (fun history =>
        arms.sum (fun action => (loss history action) ^ 2)) := by
  exact
    actionProcess_integral_mixedSquaredImportanceWeightedLoss_eq_integral_sum_loss_sq
      historyMu arms prob loss source
      (fun history action haction => regularity.prob_pos history action haction)
      (measurable_mixedSquaredImportanceWeightedLoss_score arms prob loss source
        epsilon regularity)
      (integrable_mixedSquaredImportanceWeightedLoss_score historyMu arms prob
        loss source epsilon regularity)

end Exp3
end BanditRLProof
