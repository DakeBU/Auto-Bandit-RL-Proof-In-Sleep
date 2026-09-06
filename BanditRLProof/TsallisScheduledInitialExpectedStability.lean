import BanditRLProof.TsallisScheduledExpectedStability

/-!
# Expected scheduled half-Tsallis initial stability

This module closes the time-zero conditioning surface omitted from the
scheduled successor stability theorem.  The left side is the actual time-zero
conjugate-potential term from the scheduled pathwise decomposition.

The local rate must satisfy `0 < eta 0 <= 1 / 2`.  Rates above `1 / 2` remain a
separate fallback leaf.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Canonical time-zero conjugate-potential score on the environment and
sampled initial action. -/
noncomputable def sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) : Env × Action -> Real :=
  importanceWeightedPotentialStabilityScore arms (eta 0)
    (fun _env _candidate => (0 : Real))
    (fun _env => initialHalfTsallisDistribution arms harms (eta 0))
    loss.initial
    (sampledHalfTsallisInitialUpdatedAt arms harms (eta 0) loss)

/-- Refined time-zero budget under the canonical initial half-Tsallis law. -/
noncomputable def sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
    {Env : Type u} {Action : Type v}
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real) :
    Env -> Real :=
  refinedPotentialStabilityBound arms (eta 0)
    (fun _env => initialHalfTsallisDistribution arms harms (eta 0))

/-- The canonical time-zero history/action potential score is measurable. -/
theorem measurable_sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) :
    Measurable
      (sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
        arms harms eta loss) := by
  unfold sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
  apply measurable_importanceWeightedPotentialStabilityScore
  · intro candidate _hcandidate
    exact measurable_const
  · intro candidate _hcandidate
    exact measurable_const
  · intro candidate _hcandidate
    exact loss.measurable_initial.comp
      (measurable_id.prodMk measurable_const)
  · intro candidate hcandidate
    exact measurable_sampledHalfTsallisInitialUpdatedAt
      arms harms (eta 0) loss candidate hcandidate

/-- The time-zero refined budget is integrable under any finite environment
law when the initial rate is positive. -/
theorem integrable_sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (heta : 0 < eta 0) :
    Integrable
      (sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
        (Env := Env) arms harms eta) prior := by
  unfold sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
  exact integrable_refinedPotentialStabilityBound_of_finiteSimplex
    prior arms (eta 0)
      (fun _env : Env => initialHalfTsallisDistribution arms harms (eta 0))
      (initialHalfTsallisEnvironmentDistributionSource
        (Env := Env) arms harms (eta 0)) heta

/-- The actual scheduled time-zero potential term agrees almost surely with
the canonical environment/action score. -/
theorem sampledScheduledHalfTsallisPotentialStabilityAtTime_zero_eq_initial_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    (fun sample => sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta sample 0) =ᵐ[mu]
      (fun sample =>
        sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
          arms harms eta loss (sample.1, (sample.2 0).1)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let algorithm := sampledScheduledHalfTsallisHistoryAlgorithm
    arms harms eta selector.finiteHistory
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hreward :=
    Exp3.canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
      prior algorithm loss
  have hreward' :
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 0).2) =ᵐ[mu]
      (fun sample => loss.initial sample.1 (sample.2 0).1) := by
    simpa [mu, algorithm, sampledScheduledHalfTsallisTrajectoryKernel] using
      hreward
  filter_upwards [hreward'] with sample hrewardSample
  have hestimate :
      sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta 0 sample =
        Exp3.importanceWeightedLoss
          (initialHalfTsallisDistribution arms harms (eta 0))
          (loss.initial sample.1) (sample.2 0).1 := by
    funext candidate
    unfold sampledScheduledHalfTsallisObservedEstimatedLossAt
      sampledScheduledHalfTsallisProbabilityAtTime
    by_cases hchosen : (sample.2 0).1 = candidate
    · simp [Exp3.importanceWeightedLoss, hchosen, hrewardSample]
    · simp [Exp3.importanceWeightedLoss, hchosen]
  have hnext :
      sampledScheduledHalfTsallisSameRateNextAt
          arms harms eta sample 0 =
        sampledHalfTsallisInitialUpdatedAt
          arms harms (eta 0) loss sample.1 (sample.2 0).1 := by
    unfold sampledScheduledHalfTsallisSameRateNextAt
      halfTsallisScheduledSameRateNext
      sampledHalfTsallisInitialUpdatedAt
      halfTsallisHistoryUpdatedMinimizer halfTsallisUpdatedMinimizer
    rw [FTRL.cumulativeLoss_succ]
    simp only [FTRL.cumulativeLoss_zero, zero_add]
    rw [hestimate]
    simp [initialHalfTsallisDistribution]
  unfold sampledScheduledHalfTsallisPotentialStabilityAtTime
    sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
    importanceWeightedPotentialStabilityScore
  dsimp only
  rw [hestimate, hnext]
  simp [FTRL.cumulativeLoss_zero,
    sampledScheduledHalfTsallisProbabilityAtTime]
  congr 1

/-!
The scheduled time-zero expected stability bound.  It uses only the canonical
initial action law and deterministic predictable initial reward.  No schedule
monotonicity, probability floor, or successor-round premise is required.
-/
theorem integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_refined
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (heta : 0 < eta 0) (heta_le : eta 0 <= 1 / 2)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample 0) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample 0) <=
        integral mu (fun sample =>
          sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
            (Env := Env) arms harms eta sample.1) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let algorithm := sampledScheduledHalfTsallisHistoryAlgorithm
    arms harms eta selector.finiteHistory
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let score := fun _env : Env => fun _candidate : Action => (0 : Real)
  let prob := fun _env : Env =>
    initialHalfTsallisDistribution arms harms (eta 0)
  let roundLoss := loss.initial
  let next := sampledHalfTsallisInitialUpdatedAt arms harms (eta 0) loss
  let source := initialHalfTsallisEnvironmentDistributionSource
    (Env := Env) arms harms (eta 0)
  let policy := Exp3.finiteActionKernel arms prob source
  have hhistory : Measurable history := measurable_fst
  have haction : Measurable action :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  have hkernel : Kernel.const Env algorithm.initialAction = policy := by
    ext env event hevent
    rw [Kernel.const_apply, Exp3.finiteActionKernel_apply]
    rfl
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    have hbase :=
      Exp3.canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
        prior algorithm loss.environment
    rw [hkernel] at hbase
    simpa [mu, algorithm, history, action,
      sampledScheduledHalfTsallisTrajectoryKernel] using hbase
  have hpolicy : policy =ᵐ[mu.map history]
      fun env => Exp3.finiteActionMeasure arms (prob env) :=
    Exp3.finiteActionKernel_ae_eq_finiteActionMeasure
      (mu.map history) arms prob source
  have hprobMin (env : Env) :
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta 0) (negEntropyRegularizer arms (1 / 2 : Real))
        (score env) (prob env) :=
    halfTsallisMinimizer_isRegularizedMinimizer
      arms harms (eta 0) (score env)
  have hnextMin (env : Env) (chosen : Action) (_hchosen : chosen ∈ arms) :
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta 0) (negEntropyRegularizer arms (1 / 2 : Real))
        (fun candidate => score env candidate +
          Exp3.importanceWeightedLoss
            (prob env) (roundLoss env) chosen candidate)
        (next env chosen) := by
    simpa [score, prob, roundLoss, next,
      sampledHalfTsallisInitialUpdatedAt,
      halfTsallisHistoryUpdatedMinimizer] using
      (halfTsallisUpdatedMinimizer_isRegularizedMinimizer
        arms harms (eta 0) (fun _candidate => 0) (loss.initial env) chosen)
  have hloss (env : Env) (candidate : Action) (_hcandidate : candidate ∈ arms) :
      0 <= roundLoss env candidate ∧ roundLoss env candidate <= 1 :=
    loss.initial_mem_unitInterval env candidate
  have hscore : Measurable
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next) := by
    simpa [score, prob, roundLoss, next,
      sampledScheduledHalfTsallisInitialHistoryActionPotentialStability] using
      (measurable_sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
        arms harms eta loss)
  have hproduct : Integrable
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next)
      (mu.map history ⊗ₘ policy) := by
    have hfinite :=
      integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel
        (mu.map history) arms (eta 0) score prob roundLoss next source
        heta heta_le hprobMin hnextMin hloss hscore
    simpa [policy] using hfinite
  have hbound : Integrable
      (refinedPotentialStabilityBound arms (eta 0) prob)
      (mu.map history) :=
    integrable_refinedPotentialStabilityBound_of_finiteSimplex
      (mu.map history) arms (eta 0) prob source heta
  have hcanonical :=
    integral_importanceWeightedPotentialStabilityScore_le_integral_refinedBound_of_condDistrib_of_minimizers
      mu history hhistory action haction arms (eta 0) score prob roundLoss next
      policy hpolicy hcond heta heta_le hprobMin hnextMin hloss hscore hproduct
      hbound
  have hscoreComp : Integrable (fun sample =>
      importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next
        (history sample, action sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu history hhistory action haction
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next)
      policy hcond hproduct
  have hterm :=
    sampledScheduledHalfTsallisPotentialStabilityAtTime_zero_eq_initial_ae
      prior arms harms eta loss
  dsimp only at hterm
  have hterm' :
      (fun sample => sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample 0) =ᵐ[mu]
      (fun sample => importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next
        (history sample, action sample)) := by
    simpa [mu, selector, history, action, score, prob, roundLoss, next,
      sampledScheduledHalfTsallisInitialHistoryActionPotentialStability] using
      hterm
  refine ⟨hscoreComp.congr hterm'.symm, ?_⟩
  calc
    integral mu (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample 0) =
      integral mu (fun sample =>
        importanceWeightedPotentialStabilityScore
          arms (eta 0) score prob roundLoss next
          (history sample, action sample)) := integral_congr_ae hterm'
    _ <= integral (mu.map history)
        (refinedPotentialStabilityBound arms (eta 0) prob) := hcanonical
    _ = integral mu (fun sample =>
        sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
          (Env := Env) arms harms eta sample.1) := by
      rw [integral_map hhistory.aemeasurable hbound.aestronglyMeasurable]
      rfl

end Tsallis
end BanditRLProof
