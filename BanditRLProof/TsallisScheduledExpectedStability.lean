import BanditRLProof.TsallisScheduledScoreAlignment
import BanditRLProof.TsallisConjugatePotentialFiniteHorizon

/-!
# Expected scheduled half-Tsallis successor stability

This module transports the one-round ordinary-importance-weighted
conjugate-potential bound through the generated scheduled action law.  Round
`n + 1` uses `eta (n + 1)`, so the finite sum can vary the learning rate
without weakening the deterministic stability theorem.

Only successor rounds are treated here.  The initial action has a different
conditioning surface and remains a separate leaf.  Rates above `1 / 2` also
remain outside this theorem.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Visible environment/pair-history state before scheduled action `n + 1`. -/
def sampledScheduledHalfTsallisHistoryAt
    {Env : Type u} {Action : Type v}
    (n : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    Env × History.FinitePairHistory Action Real n :=
  (sample.1, Preorder.frestrictLe n sample.2)

/-- Scheduled successor action after the visible prefix through `n`. -/
def sampledScheduledHalfTsallisActionAt
    {Env : Type u} {Action : Type v}
    (n : Nat) (sample : Env × ((k : Nat) -> Action × Real)) : Action :=
  (sample.2 (n + 1)).1

/-- Scheduled recursive score on an environment/prefix state. -/
noncomputable def sampledScheduledHalfTsallisScoreAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Action -> Real :=
  fun input =>
    sampledScheduledHalfTsallisHistoryScore arms harms eta n input.2

/-- Predictable successor loss on a scheduled environment/prefix state. -/
def sampledScheduledHalfTsallisPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Action -> Real :=
  fun input => loss.successor n input.1 input.2

/-- Scheduled successor probability on an environment/prefix state. -/
noncomputable def sampledScheduledHalfTsallisProbabilityAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Action -> Real :=
  fun input =>
    sampledScheduledHalfTsallisHistoryDistribution arms harms eta n input.2

/-- Same-rate canonical update after sampling scheduled action `n + 1`. -/
noncomputable def sampledScheduledHalfTsallisUpdatedAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (loss : Exp3.PredictableLossVector Env Action)
    (n : Nat) :
    Env × History.FinitePairHistory Action Real n ->
      Action -> Action -> Real :=
  halfTsallisHistoryUpdatedMinimizer arms harms (eta (n + 1))
    (sampledScheduledHalfTsallisScoreAt arms harms eta n)
    (sampledScheduledHalfTsallisPredictableLossAt loss n)

/-- Environment-lifted measurable scheduled probability source. -/
noncomputable def sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    Exp3.MeasurableFiniteActionDistribution arms
      (sampledScheduledHalfTsallisProbabilityAt
        (Env := Env) arms harms eta n) := by
  let localSource := sampledScheduledHalfTsallisHistoryDistributionSource
    arms harms eta selector n
  exact {
    distribution := fun input => localSource.distribution input.2
    measurable_prob := fun action haction =>
      (localSource.measurable_prob action haction).comp measurable_snd
  }

/-- The scheduled policy comapped to the environment/prefix state. -/
noncomputable def sampledScheduledHalfTsallisPolicyAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    Kernel (Env × History.FinitePairHistory Action Real n) Action :=
  ((sampledScheduledHalfTsallisHistoryAlgorithm
    arms harms eta selector).policy n).comap
      (fun input : Env × History.FinitePairHistory Action Real n => input.2)
      measurable_snd

instance instSampledScheduledHalfTsallisPolicyAtIsMarkov
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    IsMarkovKernel (sampledScheduledHalfTsallisPolicyAt
      (Env := Env) arms harms eta selector n) := by
  unfold sampledScheduledHalfTsallisPolicyAt
  infer_instance

/-- The environment-lifted scheduled policy is the corresponding finite
action kernel. -/
theorem sampledScheduledHalfTsallisPolicyAt_eq_finiteActionKernel
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    sampledScheduledHalfTsallisPolicyAt
        (Env := Env) arms harms eta selector n =
      Exp3.finiteActionKernel arms
        (sampledScheduledHalfTsallisProbabilityAt
          (Env := Env) arms harms eta n)
        (sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
          (Env := Env) arms harms eta selector n) := by
  ext input event hevent
  rw [sampledScheduledHalfTsallisPolicyAt, Kernel.comap_apply,
    sampledScheduledHalfTsallisHistoryAlgorithm_policy,
    Exp3.finiteActionKernel_apply, Exp3.finiteActionKernel_apply]
  rfl

/-- Coordinate regularity for the scheduled current and same-rate updated
selectors. -/
structure HalfTsallisScheduleGeneratedSelectorMeasurability
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) : Prop where
  finiteHistory : HalfTsallisScheduleFiniteHistorySelectorMeasurability
    arms harms eta
  measurable_updated : forall n candidate, candidate ∈ arms ->
    Measurable (fun sample :
        (Env × History.FinitePairHistory Action Real n) × Action =>
      sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n
        sample.1 sample.2 candidate)

/-- Every supported coordinate of the scheduled same-rate update is
measurable. -/
theorem measurable_sampledScheduledHalfTsallisUpdatedAt_canonical
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun sample :
        (Env × History.FinitePairHistory Action Real n) × Action =>
      sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n
        sample.1 sample.2 candidate) := by
  let finiteSelector :=
    canonicalHalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta
  let updatedScore :
      ((Env × History.FinitePairHistory Action Real n) × Action) ->
        Action -> Real :=
    fun sample selected =>
      sampledScheduledHalfTsallisScoreAt arms harms eta n
          sample.1 selected +
        Exp3.importanceWeightedLoss
          (sampledScheduledHalfTsallisProbabilityAt
            arms harms eta n sample.1)
          (sampledScheduledHalfTsallisPredictableLossAt loss n sample.1)
          sample.2 selected
  have hupdatedScore : forall selected, selected ∈ arms ->
      Measurable (fun sample => updatedScore sample selected) := by
    intro selected hselected
    have hscore : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledScheduledHalfTsallisScoreAt arms harms eta n
          sample.1 selected) :=
      (measurable_sampledScheduledHalfTsallisHistoryScore
        arms harms eta finiteSelector n selected hselected).comp
          (measurable_snd.comp measurable_fst)
    have hprob : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledScheduledHalfTsallisProbabilityAt arms harms eta n
          sample.1 selected) :=
      ((sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta finiteSelector n).measurable_prob
          selected hselected).comp measurable_fst
    have hloss : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledScheduledHalfTsallisPredictableLossAt loss n
          sample.1 selected) :=
      (measurable_sampledHalfTsallisPredictableLossAt loss n selected).comp
        measurable_fst
    have hincrement : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        Exp3.importanceWeightedLoss
          (sampledScheduledHalfTsallisProbabilityAt
            arms harms eta n sample.1)
          (sampledScheduledHalfTsallisPredictableLossAt loss n sample.1)
          sample.2 selected) := by
      unfold Exp3.importanceWeightedLoss
      refine Measurable.ite ?_ (hloss.div hprob) measurable_const
      simpa only [Set.mem_setOf_eq] using
        measurable_snd (measurableSet_singleton selected)
    exact hscore.add hincrement
  have hcanonical : Measurable (fun sample =>
      halfTsallisMinimizer arms harms (eta (n + 1))
        (updatedScore sample) candidate) :=
    measurable_halfTsallisMinimizer_comp arms harms (eta (n + 1))
      updatedScore hupdatedScore candidate hcandidate
  simpa only [updatedScore, sampledScheduledHalfTsallisUpdatedAt,
    halfTsallisHistoryUpdatedMinimizer, halfTsallisUpdatedMinimizer] using
      hcanonical

/-- The canonical scheduled selector satisfies current and updated coordinate
measurability at every successor round. -/
noncomputable def canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) :
    HalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss where
  finiteHistory :=
    canonicalHalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta
  measurable_updated :=
    measurable_sampledScheduledHalfTsallisUpdatedAt_canonical
      arms harms eta loss

/-- Scheduled one-round conjugate-potential score on a visible prefix and
sampled successor action. -/
noncomputable def sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    (Env × History.FinitePairHistory Action Real n) × Action -> Real :=
  importanceWeightedPotentialStabilityScore arms (eta (n + 1))
    (sampledScheduledHalfTsallisScoreAt arms harms eta n)
    (sampledScheduledHalfTsallisProbabilityAt arms harms eta n)
    (sampledScheduledHalfTsallisPredictableLossAt loss n)
    (sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n)

/-- Refined one-round budget for scheduled successor action `n + 1`. -/
noncomputable def sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Real :=
  refinedPotentialStabilityBound arms (eta (n + 1))
    (sampledScheduledHalfTsallisProbabilityAt arms harms eta n)

/-- The canonical scheduled successor potential score is measurable. -/
theorem measurable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    Measurable (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta loss n) := by
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  unfold sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
  apply measurable_importanceWeightedPotentialStabilityScore
  · intro candidate hcandidate
    exact (measurable_sampledScheduledHalfTsallisHistoryScore
      arms harms eta selector.finiteHistory n candidate hcandidate).comp
        measurable_snd
  · intro candidate hcandidate
    exact (sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
      (Env := Env) arms harms eta selector.finiteHistory n).measurable_prob
        candidate hcandidate
  · intro candidate _hcandidate
    exact measurable_sampledHalfTsallisPredictableLossAt loss n candidate
  · intro candidate hcandidate
    exact selector.measurable_updated n candidate hcandidate

/-- The scheduled refined budget is automatically integrable under any
finite visible-history law when its local rate is positive. -/
theorem integrable_sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (n : Nat)
    (historyMu : Measure (Env × History.FinitePairHistory Action Real n))
    [IsFiniteMeasure historyMu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (heta : 0 < eta (n + 1))
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) :
    Integrable
      (sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n) historyMu := by
  unfold sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
  exact integrable_refinedPotentialStabilityBound_of_finiteSimplex
    historyMu arms (eta (n + 1))
      (sampledScheduledHalfTsallisProbabilityAt
        (Env := Env) arms harms eta n)
      (sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta selector n) heta

/-- The canonical scheduled successor potential score is automatically
integrable under its visible-history/action product law. -/
theorem integrable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (n + 1)) (heta_le : eta (n + 1) <= 1 / 2) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n) ⊗ₘ
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hfinite :=
    integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel
      (mu.map (sampledScheduledHalfTsallisHistoryAt n))
      arms (eta (n + 1))
      (sampledScheduledHalfTsallisScoreAt arms harms eta n)
      (sampledScheduledHalfTsallisProbabilityAt
        (Env := Env) arms harms eta n)
      (sampledScheduledHalfTsallisPredictableLossAt loss n)
      (sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n)
      (sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta selector.finiteHistory n)
      heta heta_le
      (fun input => halfTsallisMinimizer_isRegularizedMinimizer
        arms harms (eta (n + 1))
          (sampledScheduledHalfTsallisScoreAt arms harms eta n input))
      (fun input chosen _ =>
        halfTsallisUpdatedMinimizer_isRegularizedMinimizer
          arms harms (eta (n + 1))
          (sampledScheduledHalfTsallisScoreAt arms harms eta n input)
          (sampledScheduledHalfTsallisPredictableLossAt loss n input) chosen)
      (fun input candidate _ =>
        loss.successor_mem_unitInterval n input.1 input.2 candidate)
      (measurable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
  rw [sampledScheduledHalfTsallisPolicyAt_eq_finiteActionKernel
    arms harms eta selector.finiteHistory n]
  simpa [sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt,
    mu, selector] using hfinite

/-- The actual scheduled successor potential term agrees almost surely with
the canonical visible-history/action potential score. -/
theorem sampledScheduledHalfTsallisPotentialStabilityAtTime_succ_eq_historyAction_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    (fun sample => sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta sample (n + 1)) =ᵐ[mu]
      (fun sample =>
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hreward :=
    Exp3.canonicalPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
      prior
      (sampledScheduledHalfTsallisHistoryAlgorithm
        arms harms eta selector.finiteHistory)
      loss n
  have hreward' :
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 (n + 1)).2) =ᵐ[mu]
      (fun sample => loss.successor n sample.1
        (Preorder.frestrictLe n sample.2)
        (sample.2 (n + 1)).1) := by
    simpa [mu, sampledScheduledHalfTsallisTrajectoryKernel] using hreward
  filter_upwards [hreward'] with sample hrewardSample
  have hcumulative :
      FTRL.cumulativeLoss
          (fun t => sampledScheduledHalfTsallisObservedEstimatedLossAt
            arms harms eta t sample) (n + 1) =
        sampledScheduledHalfTsallisHistoryScore arms harms eta n
          (Preorder.frestrictLe n sample.2) :=
    cumulativeLoss_sampledScheduledHalfTsallisObservedEstimatedLossAt_succ
      arms harms eta sample n
  have hestimate :
      sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta (n + 1) sample =
        Exp3.importanceWeightedLoss
          (sampledScheduledHalfTsallisHistoryDistribution
            arms harms eta n (Preorder.frestrictLe n sample.2))
          (loss.successor n sample.1
            (Preorder.frestrictLe n sample.2))
          (sample.2 (n + 1)).1 := by
    funext candidate
    unfold sampledScheduledHalfTsallisObservedEstimatedLossAt
      sampledScheduledHalfTsallisProbabilityAtTime
    by_cases hchosen : (sample.2 (n + 1)).1 = candidate
    · simp [Exp3.importanceWeightedLoss, hchosen, hrewardSample]
    · simp [Exp3.importanceWeightedLoss, hchosen]
  have hnext :
      sampledScheduledHalfTsallisSameRateNextAt
          arms harms eta sample (n + 1) =
        sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample)
          (sampledScheduledHalfTsallisActionAt n sample) := by
    unfold sampledScheduledHalfTsallisSameRateNextAt
      halfTsallisScheduledSameRateNext
      sampledScheduledHalfTsallisUpdatedAt
      halfTsallisHistoryUpdatedMinimizer halfTsallisUpdatedMinimizer
    rw [FTRL.cumulativeLoss_succ, hcumulative, hestimate]
    rfl
  unfold sampledScheduledHalfTsallisPotentialStabilityAtTime
    sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
    importanceWeightedPotentialStabilityScore
    sampledScheduledHalfTsallisScoreAt
    sampledScheduledHalfTsallisProbabilityAt
    sampledScheduledHalfTsallisPredictableLossAt
    sampledScheduledHalfTsallisHistoryAt
    sampledScheduledHalfTsallisActionAt
  dsimp only
  simp only [sampledScheduledHalfTsallisProbabilityAtTime]
  rw [hcumulative, hestimate, hnext]
  rfl

/--
Expected finite-horizon refined stability for all generated successor rounds.

The left side is exactly the same-rate stability sum consumed by the pathwise
scheduled score/penalty decomposition, restricted to actual times `n + 1`.
Time zero and rates above `1 / 2` are deliberately not claimed.
-/
theorem integral_sum_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_refined
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real)
    (heta : forall n, n < horizon -> 0 < eta (n + 1))
    (heta_le : forall n, n < horizon -> eta (n + 1) <= 1 / 2)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1))) <=
      integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample))) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hhistory (n : Nat) : Measurable
      (sampledScheduledHalfTsallisHistoryAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction (n : Nat) : Measurable
      (sampledScheduledHalfTsallisActionAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.comp
      ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hpolicy (n : Nat) :
      sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n =ᵐ[
        mu.map (sampledScheduledHalfTsallisHistoryAt n)]
        fun input => Exp3.finiteActionMeasure arms
          (sampledScheduledHalfTsallisProbabilityAt
            (Env := Env) arms harms eta n input) := by
    filter_upwards [] with input
    rw [sampledScheduledHalfTsallisPolicyAt_eq_finiteActionKernel,
      Exp3.finiteActionKernel_apply]
  have hcond (n : Nat) :
      condDistrib
          (sampledScheduledHalfTsallisActionAt
            (Env := Env) (Action := Action) n)
          (sampledScheduledHalfTsallisHistoryAt n) mu =ᵐ[
        mu.map (sampledScheduledHalfTsallisHistoryAt n)]
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n := by
    simpa [mu, sampledScheduledHalfTsallisHistoryAt,
      sampledScheduledHalfTsallisActionAt,
      sampledScheduledHalfTsallisPolicyAt] using
      (sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta selector.finiteHistory loss.environment n)
  have hscore (n : Nat) : Measurable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n) :=
    measurable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta loss n
  have hproduct (n : Nat) (hn : n < horizon) : Integrable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n) ⊗ₘ
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n) := by
    simpa [mu, selector] using
      (integrable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        prior arms harms eta loss n (heta n hn) (heta_le n hn))
  have hbound (n : Nat) (hn : n < horizon) : Integrable
      (sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n)) :=
    integrable_sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
      n (mu.map (sampledScheduledHalfTsallisHistoryAt n))
      arms harms eta (heta n hn) selector.finiteHistory
  have hscoreComp (n : Nat) (hn : n < horizon) : Integrable (fun sample =>
      sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n
        (sampledScheduledHalfTsallisHistoryAt n sample,
          sampledScheduledHalfTsallisActionAt n sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu (sampledScheduledHalfTsallisHistoryAt n) (hhistory n)
      (sampledScheduledHalfTsallisActionAt n) (haction n)
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (sampledScheduledHalfTsallisPolicyAt (Env := Env)
        arms harms eta selector.finiteHistory n)
      (hcond n) (hproduct n hn)
  have hboundComp (n : Nat) (hn : n < horizon) : Integrable (fun sample =>
      sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n
        (sampledScheduledHalfTsallisHistoryAt n sample)) mu := by
    simpa [Function.comp_def] using
      (hbound n hn).comp_measurable (hhistory n)
  have hround (n : Nat) (hn : n < horizon) :
      integral mu (fun sample =>
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample)) <=
      integral mu (fun sample =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample)) := by
    have h :=
      integral_importanceWeightedPotentialStabilityScore_le_integral_refinedBound_of_condDistrib_of_minimizers
        mu (sampledScheduledHalfTsallisHistoryAt n) (hhistory n)
        (sampledScheduledHalfTsallisActionAt n) (haction n)
        arms (eta (n + 1))
        (sampledScheduledHalfTsallisScoreAt arms harms eta n)
        (sampledScheduledHalfTsallisProbabilityAt
          (Env := Env) arms harms eta n)
        (sampledScheduledHalfTsallisPredictableLossAt loss n)
        (sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n)
        (sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n)
        (hpolicy n) (hcond n) (heta n hn) (heta_le n hn)
        (fun input => halfTsallisMinimizer_isRegularizedMinimizer
          arms harms (eta (n + 1))
            (sampledScheduledHalfTsallisScoreAt arms harms eta n input))
        (fun input chosen _ =>
          halfTsallisUpdatedMinimizer_isRegularizedMinimizer
            arms harms (eta (n + 1))
            (sampledScheduledHalfTsallisScoreAt arms harms eta n input)
            (sampledScheduledHalfTsallisPredictableLossAt loss n input)
            chosen)
        (fun input candidate _ =>
          loss.successor_mem_unitInterval n input.1 input.2 candidate)
        (hscore n) (hproduct n hn) (hbound n hn)
    calc
      integral mu (fun sample =>
          sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
            arms harms eta loss n
            (sampledScheduledHalfTsallisHistoryAt n sample,
              sampledScheduledHalfTsallisActionAt n sample)) <=
        integral (mu.map (sampledScheduledHalfTsallisHistoryAt n))
          (sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
            (Env := Env) arms harms eta n) := by
          simpa [sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt,
            sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt]
            using h
      _ = integral mu (fun sample =>
          sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
            (Env := Env) arms harms eta n
            (sampledScheduledHalfTsallisHistoryAt n sample)) := by
        rw [integral_map (hhistory n).aemeasurable
          (hbound n hn).aestronglyMeasurable]
  have hterm (n : Nat) :
      (fun sample => sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample (n + 1)) =ᵐ[mu]
      (fun sample =>
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample)) := by
    have hreward :=
      Exp3.canonicalPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
        prior
        (sampledScheduledHalfTsallisHistoryAlgorithm
          arms harms eta selector.finiteHistory)
        loss n
    have hreward' :
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 (n + 1)).2) =ᵐ[mu]
        (fun sample => loss.successor n sample.1
          (Preorder.frestrictLe n sample.2)
          (sample.2 (n + 1)).1) := by
      simpa [mu, sampledScheduledHalfTsallisTrajectoryKernel] using hreward
    filter_upwards [hreward'] with sample hrewardSample
    have hcumulative :
        FTRL.cumulativeLoss
            (fun t => sampledScheduledHalfTsallisObservedEstimatedLossAt
              arms harms eta t sample) (n + 1) =
          sampledScheduledHalfTsallisHistoryScore arms harms eta n
            (Preorder.frestrictLe n sample.2) :=
      cumulativeLoss_sampledScheduledHalfTsallisObservedEstimatedLossAt_succ
        arms harms eta sample n
    have hestimate :
        sampledScheduledHalfTsallisObservedEstimatedLossAt
            arms harms eta (n + 1) sample =
          Exp3.importanceWeightedLoss
            (sampledScheduledHalfTsallisHistoryDistribution
              arms harms eta n (Preorder.frestrictLe n sample.2))
            (loss.successor n sample.1
              (Preorder.frestrictLe n sample.2))
            (sample.2 (n + 1)).1 := by
      funext candidate
      unfold sampledScheduledHalfTsallisObservedEstimatedLossAt
        sampledScheduledHalfTsallisProbabilityAtTime
      by_cases hchosen : (sample.2 (n + 1)).1 = candidate
      · simp [Exp3.importanceWeightedLoss, hchosen, hrewardSample]
      · simp [Exp3.importanceWeightedLoss, hchosen]
    have hnext :
        sampledScheduledHalfTsallisSameRateNextAt
            arms harms eta sample (n + 1) =
          sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n
            (sampledScheduledHalfTsallisHistoryAt n sample)
            (sampledScheduledHalfTsallisActionAt n sample) := by
      unfold sampledScheduledHalfTsallisSameRateNextAt
        halfTsallisScheduledSameRateNext
        sampledScheduledHalfTsallisUpdatedAt
        halfTsallisHistoryUpdatedMinimizer halfTsallisUpdatedMinimizer
      rw [FTRL.cumulativeLoss_succ, hcumulative, hestimate]
      rfl
    unfold sampledScheduledHalfTsallisPotentialStabilityAtTime
      sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
      importanceWeightedPotentialStabilityScore
      sampledScheduledHalfTsallisScoreAt
      sampledScheduledHalfTsallisProbabilityAt
      sampledScheduledHalfTsallisPredictableLossAt
      sampledScheduledHalfTsallisHistoryAt
      sampledScheduledHalfTsallisActionAt
    dsimp only
    simp only [sampledScheduledHalfTsallisProbabilityAtTime]
    rw [hcumulative, hestimate, hnext]
    rfl
  have htermAll : ∀ᵐ sample ∂mu, forall n,
      sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1) =
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample) := by
    rw [ae_all_iff]
    exact hterm
  calc
    integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1))) =
      integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample))) := by
      apply integral_congr_ae
      filter_upwards [htermAll] with sample hsample
      exact Finset.sum_congr rfl fun n _ => hsample n
    _ = (Finset.range horizon).sum (fun n => integral mu (fun sample =>
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample))) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon) _
        (fun n hn => hscoreComp n (Finset.mem_range.mp hn))
    _ <= (Finset.range horizon).sum (fun n => integral mu (fun sample =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample))) := by
      exact Finset.sum_le_sum fun n hn =>
        hround n (Finset.mem_range.mp hn)
    _ = integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample))) := by
      symm
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon) _
        (fun n hn => hboundComp n (Finset.mem_range.mp hn))

end Tsallis
end BanditRLProof
