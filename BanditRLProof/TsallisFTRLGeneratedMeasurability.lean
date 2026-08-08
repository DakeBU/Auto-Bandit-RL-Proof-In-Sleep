import BanditRLProof.TsallisFTRLGeneratedRegularity
import BanditRLProof.TsallisFTRLMinimizerMeasurability

/-!
# Generated half-Tsallis stability measurability

This module derives measurability of the generated one-round stability score
from coordinate measurability of the current and updated half-Tsallis
selectors.  The updated selector remains noncomputable, so its coordinate
measurability is kept as an explicit selector contract rather than inferred
from `Classical.choose`.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Coordinate regularity for the generated current and sampled-action updated
half-Tsallis selectors.  The finite-history component constructs the policy;
the second component covers the environment/prefix/action parameter space of
the updated canonical minimizer. -/
structure HalfTsallisGeneratedSelectorMeasurability
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action) : Prop where
  finiteHistory :
    HalfTsallisFiniteHistorySelectorMeasurability arms harms eta
  measurable_updated : forall n candidate, candidate ∈ arms ->
    Measurable (fun sample :
        (Env × History.FinitePairHistory Action Real n) × Action =>
      sampledHalfTsallisUpdatedAt arms harms eta loss n
        sample.1 sample.2 candidate)

/-- The canonical half-Tsallis selector itself satisfies the finite-history
coordinate measurability contract. -/
noncomputable def canonicalHalfTsallisFiniteHistorySelectorMeasurability
    {Action : Type v} [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real) :
    HalfTsallisFiniteHistorySelectorMeasurability arms harms eta where
  measurable_selector := by
    intro n score hscore action haction
    exact measurable_halfTsallisMinimizer_comp
      arms harms eta score hscore action haction

/-- A finite sum of current-minus-updated importance-weighted linear losses is
measurable once all current, loss, and updated coordinates are measurable. -/
theorem measurable_importanceWeightedStabilityScore
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action)
    (prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (hprob : forall candidate, candidate ∈ arms ->
      Measurable (fun history => prob history candidate))
    (hloss : forall candidate, candidate ∈ arms ->
      Measurable (fun history => loss history candidate))
    (hnext : forall candidate, candidate ∈ arms ->
      Measurable (fun sample : History × Action =>
        next sample.1 sample.2 candidate)) :
    Measurable (importanceWeightedStabilityScore arms prob loss next) := by
  classical
  unfold importanceWeightedStabilityScore FTRL.linearLoss
  apply (Finset.measurable_sum arms fun candidate hcandidate => ?_).sub
    (Finset.measurable_sum arms fun candidate hcandidate => ?_)
  · have hestimated : Measurable (fun sample : History × Action =>
        Exp3.importanceWeightedLoss (prob sample.1) (loss sample.1)
          sample.2 candidate) := by
      unfold Exp3.importanceWeightedLoss
      refine Measurable.ite ?_
        (((hloss candidate hcandidate).comp measurable_fst).div
          ((hprob candidate hcandidate).comp measurable_fst))
        measurable_const
      simpa only [Set.mem_setOf_eq] using
        measurable_snd (measurableSet_singleton candidate)
    exact ((hprob candidate hcandidate).comp measurable_fst).mul hestimated
  · have hestimated : Measurable (fun sample : History × Action =>
        Exp3.importanceWeightedLoss (prob sample.1) (loss sample.1)
          sample.2 candidate) := by
      unfold Exp3.importanceWeightedLoss
      refine Measurable.ite ?_
        (((hloss candidate hcandidate).comp measurable_fst).div
          ((hprob candidate hcandidate).comp measurable_fst))
        measurable_const
      simpa only [Set.mem_setOf_eq] using
        measurable_snd (measurableSet_singleton candidate)
    exact (hnext candidate hcandidate).mul hestimated

/-- Every supported coordinate of the generated predictable loss vector is
measurable on the environment/prefix parameter space. -/
theorem measurable_sampledHalfTsallisPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (candidate : Action) :
    Measurable (fun input :
        Env × History.FinitePairHistory Action Real n =>
      sampledHalfTsallisPredictableLossAt loss n input candidate) := by
  simpa only [sampledHalfTsallisPredictableLossAt] using
    (loss.measurable_successor n).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

/-- Every supported coordinate of the canonical sampled-action update is
measurable without an external selector assumption. -/
theorem measurable_sampledHalfTsallisUpdatedAt_canonical
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun sample :
        (Env × History.FinitePairHistory Action Real n) × Action =>
      sampledHalfTsallisUpdatedAt arms harms eta loss n
        sample.1 sample.2 candidate) := by
  let finiteSelector : HalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta :=
    canonicalHalfTsallisFiniteHistorySelectorMeasurability arms harms eta
  let updatedScore :
      ((Env × History.FinitePairHistory Action Real n) × Action) ->
        Action -> Real :=
    fun sample selected =>
      sampledHalfTsallisScoreAt arms harms eta n sample.1 selected +
        Exp3.importanceWeightedLoss
          (sampledHalfTsallisProbabilityAt arms harms eta n sample.1)
          (sampledHalfTsallisPredictableLossAt loss n sample.1)
          sample.2 selected
  have hupdatedScore : forall selected, selected ∈ arms ->
      Measurable (fun sample => updatedScore sample selected) := by
    intro selected hselected
    have hscore : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledHalfTsallisScoreAt arms harms eta n sample.1 selected) :=
      (measurable_sampledHalfTsallisHistoryScore
        arms harms eta finiteSelector n selected hselected).comp
          (measurable_snd.comp measurable_fst)
    have hprob : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledHalfTsallisProbabilityAt arms harms eta n
          sample.1 selected) :=
      ((sampledHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta finiteSelector n).measurable_prob
          selected hselected).comp measurable_fst
    have hloss : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledHalfTsallisPredictableLossAt loss n
          sample.1 selected) :=
      (measurable_sampledHalfTsallisPredictableLossAt loss n selected).comp
        measurable_fst
    have hincrement : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        Exp3.importanceWeightedLoss
          (sampledHalfTsallisProbabilityAt arms harms eta n sample.1)
          (sampledHalfTsallisPredictableLossAt loss n sample.1)
          sample.2 selected) := by
      unfold Exp3.importanceWeightedLoss
      refine Measurable.ite ?_ (hloss.div hprob) measurable_const
      simpa only [Set.mem_setOf_eq] using
        measurable_snd (measurableSet_singleton selected)
    change Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
      sampledHalfTsallisScoreAt arms harms eta n sample.1 selected +
        Exp3.importanceWeightedLoss
          (sampledHalfTsallisProbabilityAt arms harms eta n sample.1)
          (sampledHalfTsallisPredictableLossAt loss n sample.1)
          sample.2 selected)
    exact hscore.add hincrement
  have hcanonical : Measurable (fun sample =>
      halfTsallisMinimizer arms harms eta
        (updatedScore sample) candidate) :=
    measurable_halfTsallisMinimizer_comp
      arms harms eta updatedScore hupdatedScore candidate hcandidate
  simpa only [updatedScore, sampledHalfTsallisUpdatedAt,
    halfTsallisHistoryUpdatedMinimizer, halfTsallisUpdatedMinimizer,
    sampledHalfTsallisProbabilityAt, halfTsallisHistoryMinimizer] using
      hcanonical

/-- The canonical current and one-step updated minimizers satisfy the full
generated-selector regularity contract; callers no longer need to assume
measurability of either `Classical.choose` surface. -/
noncomputable def canonicalHalfTsallisGeneratedSelectorMeasurability
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action) :
    HalfTsallisGeneratedSelectorMeasurability arms harms eta loss where
  finiteHistory :=
    canonicalHalfTsallisFiniteHistorySelectorMeasurability arms harms eta
  measurable_updated :=
    measurable_sampledHalfTsallisUpdatedAt_canonical arms harms eta loss

/-- The generated one-round current-minus-updated stability score is
measurable under the generated selector coordinate contract. -/
theorem measurable_sampledHalfTsallisHistoryActionStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (selector : HalfTsallisGeneratedSelectorMeasurability
      arms harms eta loss) (n : Nat) :
    Measurable (sampledHalfTsallisHistoryActionStabilityAt
      arms harms eta loss n) := by
  unfold sampledHalfTsallisHistoryActionStabilityAt
  apply measurable_importanceWeightedStabilityScore
  · intro candidate hcandidate
    exact (sampledHalfTsallisEnvironmentHistoryDistributionSource
      (Env := Env) arms harms eta selector.finiteHistory n).measurable_prob
        candidate hcandidate
  · intro candidate _hcandidate
    exact measurable_sampledHalfTsallisPredictableLossAt loss n candidate
  · intro candidate hcandidate
    exact selector.measurable_updated n candidate hcandidate

/-- Generated finite-horizon actual-successor stability with all score and
integrability regularity derived from one generated-selector contract. -/
theorem integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_of_selector
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (heta : 0 < eta)
    (loss : Exp3.PredictableLossVector Env Action)
    (selector : HalfTsallisGeneratedSelectorMeasurability
      arms harms eta loss) :
    let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisSuccessorStabilityAt
          arms harms eta loss n sample)) <=
      integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisHalfPowerBoundAt (Env := Env)
          arms harms eta n (sampledHalfTsallisHistoryAt n sample))) := by
  exact
    integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_of_measurable
      prior horizon arms harms eta heta selector.finiteHistory loss
      (fun n => measurable_sampledHalfTsallisHistoryActionStabilityAt
        arms harms eta loss selector n)

/-- Generated finite-horizon actual-successor stability for the canonical
half-Tsallis policy, with selector measurability proved internally. -/
theorem integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_canonical
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (heta : 0 < eta)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector := canonicalHalfTsallisGeneratedSelectorMeasurability
      arms harms eta loss
    let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisSuccessorStabilityAt
          arms harms eta loss n sample)) <=
      integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisHalfPowerBoundAt (Env := Env)
          arms harms eta n (sampledHalfTsallisHistoryAt n sample))) := by
  dsimp only
  exact
    integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_of_selector
      prior horizon arms harms eta heta loss
        (canonicalHalfTsallisGeneratedSelectorMeasurability
          arms harms eta loss)

end Tsallis
end BanditRLProof
