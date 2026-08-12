import BanditRLProof.Algorithms.ThompsonRecursiveSampler
import BanditRLProof.ExpectationBochnerSums

/-!
# Bayesian regret decomposition for the recursive Thompson trajectory

This module ports the probability-matching algebra behind LML's
`TS.integral_regret_eq_add` to the locally generated Thompson trajectory.
The confidence score is abstract but must depend only on the visible history
and the candidate action.  Clipped-UCB concentration can therefore be attached
downstream without restoring an assumed sampler or posterior law.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory

universe u v w x

namespace BanditRLProof
namespace Thompson

/-- A real score whose time-`n + 1` value sees exactly the history through `n`. -/
structure HistoryActionScore (Action : Type u) (Reward : Type v)
    [MeasurableSpace Action] [MeasurableSpace Reward] where
  initial : Action -> Real
  successor :
    (n : Nat) -> History.FinitePairHistory Action Reward n -> Action -> Real
  measurable_initial : Measurable initial
  measurable_successor :
    forall n, Measurable (fun pair :
      History.FinitePairHistory Action Reward n × Action =>
        successor n pair.1 pair.2)

namespace HistoryActionScore

/-- Evaluate a history score on the action selected by one complete trace. -/
def atTrace
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (score : HistoryActionScore Action Reward)
    (action : ActionTrace Action) (reward : RewardTrace Reward) :
    Nat -> Real
  | 0 => score.initial (action 0)
  | n + 1 => score.successor n
      (History.finitePairHistoryOfTrace action reward n) (action (n + 1))

/-- Evaluate the same visible-history score at a comparison action. -/
def atBestTrace
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (score : HistoryActionScore Action Reward)
    (bestAction : Action)
    (action : ActionTrace Action) (reward : RewardTrace Reward) :
    Nat -> Real
  | 0 => score.initial bestAction
  | n + 1 => score.successor n
      (History.finitePairHistoryOfTrace action reward n) bestAction

theorem measurable_atTrace
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action] [MeasurableSpace Reward]
    (score : HistoryActionScore Action Reward)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (t : Nat) :
    Measurable (fun omega => score.atTrace (action omega) (reward omega) t) := by
  cases t with
  | zero =>
      exact score.measurable_initial.comp (haction 0)
  | succ n =>
      exact (score.measurable_successor n).comp
        ((History.measurable_finitePairHistoryOfTrace
          action reward haction hreward n).prodMk (haction (n + 1)))

theorem measurable_atBestTrace
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action] [MeasurableSpace Reward]
    (score : HistoryActionScore Action Reward)
    (bestAction : Omega -> Action) (hbestAction : Measurable bestAction)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (t : Nat) :
    Measurable (fun omega =>
      score.atBestTrace (bestAction omega) (action omega) (reward omega) t) := by
  cases t with
  | zero =>
      exact score.measurable_initial.comp hbestAction
  | succ n =>
      exact (score.measurable_successor n).comp
        ((History.measurable_finitePairHistoryOfTrace
          action reward haction hreward n).prodMk hbestAction)

end HistoryActionScore

/-- Equal pushforwards give equal integrals of every measurable real score. -/
theorem integral_comp_eq_of_map_eq
    {Omega : Type u} {Target : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Target]
    (mu : Measure Omega)
    (left right : Omega -> Target)
    (hleft : Measurable left) (hright : Measurable right)
    (hmap : mu.map left = mu.map right)
    (score : Target -> Real) (hscore : Measurable score) :
    integral mu (fun omega => score (left omega)) =
      integral mu (fun omega => score (right omega)) := by
  calc
    _ = integral (mu.map left) score := by
      rw [integral_map hleft.aemeasurable hscore.aestronglyMeasurable]
    _ = integral (mu.map right) score := by rw [hmap]
    _ = _ := by
      rw [integral_map hright.aemeasurable hscore.aestronglyMeasurable]

/--
If two actions have the same conditional law given a history, every measurable
history/action score has the same expectation under those actions.
-/
theorem integral_historyAction_eq_of_condDistrib_ae_eq
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action bestAction : Omega -> Action)
    (haction : Measurable action) (hbestAction : Measurable bestAction)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      condDistrib bestAction history mu)
    (score : History × Action -> Real) (hscore : Measurable score) :
    integral mu (fun omega => score (history omega, action omega)) =
      integral mu (fun omega => score (history omega, bestAction omega)) := by
  have hpair :
      mu.map (fun omega => (history omega, action omega)) =
        mu.map (fun omega => (history omega, bestAction omega)) := by
    rw [← compProd_map_condDistrib haction.aemeasurable,
      ← compProd_map_condDistrib hbestAction.aemeasurable]
    exact Measure.compProd_congr hcond
  exact integral_comp_eq_of_map_eq mu
    (fun omega => (history omega, action omega))
    (fun omega => (history omega, bestAction omega))
    (hhistory.prodMk haction) (hhistory.prodMk hbestAction) hpair score hscore

/-- The environment-indexed trajectory kernel has the algorithm's action law at time zero. -/
theorem canonicalMeasurableEnvironmentTrajectoryKernel_map_action_zero
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment).map
        (fun trajectory => (trajectory 0).1) =
      Kernel.const Env algorithm.initialAction := by
  change
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment).map
        (Prod.fst ∘ fun trajectory => trajectory 0) =
      Kernel.const Env algorithm.initialAction
  have hevalZero : Measurable
      (fun trajectory : (n : Nat) -> Action × Reward => trajectory 0) :=
    measurable_pi_apply 0
  rw [Kernel.map_comp_right _ hevalZero measurable_fst,
    canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero,
    ← Kernel.fst_eq, measurableEnvironmentInitialPairKernel,
    Kernel.fst_compProd]

/-- Mixing the trajectory kernel through a probability prior preserves its initial action law. -/
theorem canonicalMeasurableEnvironmentTrajectoryMeasure_map_action_zero
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
      algorithm environment).map
        (fun sample => (sample.2 0).1) =
      algorithm.initialAction := by
  let trajectory :=
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  let actionZero := fun trace : (n : Nat) -> Action × Reward => (trace 0).1
  have hactionZero : Measurable actionZero :=
    measurable_fst.comp (measurable_pi_apply 0)
  calc
    (prior ⊗ₘ trajectory).map (actionZero ∘ Prod.snd) =
        ((prior ⊗ₘ trajectory).map Prod.snd).map actionZero := by
      rw [Measure.map_map (g := actionZero) (f := Prod.snd)
        hactionZero measurable_snd]
    _ = (trajectory ∘ₘ prior).map actionZero := by
      change (prior ⊗ₘ trajectory).snd.map actionZero =
        (trajectory ∘ₘ prior).map actionZero
      rw [Measure.snd_compProd]
    _ = (trajectory.map actionZero) ∘ₘ prior := by
      rw [Measure.map_comp prior trajectory hactionZero]
    _ = Kernel.const Env algorithm.initialAction ∘ₘ prior := by
      rw [canonicalMeasurableEnvironmentTrajectoryKernel_map_action_zero]
    _ = algorithm.initialAction := by
      rw [Measure.const_comp, measure_univ, one_smul]

/-- The initial action and latent best action have the same marginal on the actual TS trajectory. -/
theorem uniformReferenceThompsonAlgorithm_map_action_zero_eq_bestAction
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    let algorithm :=
      uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
    let actualMeasure :=
      prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    actualMeasure.map
        (fun sample => environmentTrajectoryAction sample 0) =
      actualMeasure.map (bestAction ∘ Prod.fst) := by
  dsimp only
  let algorithm :=
    uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
  let actualMeasure :=
    prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  have haction :
      actualMeasure.map (fun sample => environmentTrajectoryAction sample 0) =
        prior.map bestAction := by
    calc
      _ = algorithm.initialAction := by
        exact canonicalMeasurableEnvironmentTrajectoryMeasure_map_action_zero
          prior algorithm environment
      _ = prior.map bestAction := by
        simp [algorithm, uniformReferenceThompsonAlgorithm]
  have hbest :
      actualMeasure.map (bestAction ∘ Prod.fst) = prior.map bestAction := by
    calc
      _ = (actualMeasure.map Prod.fst).map bestAction := by
        rw [Measure.map_map (g := bestAction) (f := Prod.fst)
          hbestAction measurable_fst]
      _ = prior.map bestAction := by
        change
          (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
            algorithm environment).fst.map bestAction = prior.map bestAction
        rw [Measure.fst_compProd]
  exact haction.trans hbest.symm

/-- Evaluate the history score on the actual trajectory action. -/
def trajectoryHistoryScore
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (score : HistoryActionScore Action Reward)
    (sample : Env × ((n : Nat) -> Action × Reward)) (t : Nat) : Real :=
  score.atTrace (environmentTrajectoryAction sample)
    (environmentTrajectoryReward sample) t

/-- Evaluate the same score at the latent environment's best action. -/
def trajectoryBestHistoryScore
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (score : HistoryActionScore Action Reward)
    (bestAction : Env -> Action)
    (sample : Env × ((n : Nat) -> Action × Reward)) (t : Nat) : Real :=
  score.atBestTrace (bestAction sample.1)
    (environmentTrajectoryAction sample)
    (environmentTrajectoryReward sample) t

/--
Probability matching on the actual recursive trajectory implies equality of
every visible-history score at the selected and latent-best actions.
-/
theorem uniformReferenceThompsonAlgorithm_integral_historyScore_eq_bestAction
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (score : HistoryActionScore Action Reward) (t : Nat) :
    let algorithm :=
      uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
    let actualMeasure :=
      prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    integral actualMeasure (fun sample =>
        trajectoryHistoryScore score sample t) =
      integral actualMeasure (fun sample =>
        trajectoryBestHistoryScore score bestAction sample t) := by
  dsimp only
  let algorithm :=
    uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
  let actualMeasure :=
    prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  cases t with
  | zero =>
      exact integral_comp_eq_of_map_eq actualMeasure
        (fun sample => environmentTrajectoryAction sample 0)
        (bestAction ∘ Prod.fst)
        (measurable_environmentTrajectoryAction_apply 0)
        (hbestAction.comp measurable_fst)
        (uniformReferenceThompsonAlgorithm_map_action_zero_eq_bestAction
          prior environment bestAction hbestAction)
        score.initial score.measurable_initial
  | succ n =>
      let history := fun sample :
          Env × ((n : Nat) -> Action × Reward) =>
        History.finitePairHistoryOfTrace
          (environmentTrajectoryAction sample)
          (environmentTrajectoryReward sample) n
      have hhistory : Measurable history :=
        History.measurable_finitePairHistoryOfTrace
          environmentTrajectoryAction environmentTrajectoryReward
          measurable_environmentTrajectoryAction_apply
          measurable_environmentTrajectoryReward_apply n
      have hnextAction : Measurable
          (fun sample : Env × ((n : Nat) -> Action × Reward) =>
            environmentTrajectoryAction sample (n + 1)) :=
        measurable_environmentTrajectoryAction_apply (n + 1)
      have hbest : Measurable
          (fun sample : Env × ((n : Nat) -> Action × Reward) =>
            bestAction sample.1) :=
        hbestAction.comp measurable_fst
      simpa [trajectoryHistoryScore, trajectoryBestHistoryScore,
        HistoryActionScore.atTrace, HistoryActionScore.atBestTrace, history,
        actualMeasure, algorithm] using
        (integral_historyAction_eq_of_condDistrib_ae_eq
          (Omega := Env × ((n : Nat) -> Action × Reward))
          (History := History.FinitePairHistory Action Reward n)
          (Action := Action) actualMeasure
          history hhistory
          (fun sample : Env × ((n : Nat) -> Action × Reward) =>
            environmentTrajectoryAction sample (n + 1))
          (fun sample : Env × ((n : Nat) -> Action × Reward) =>
            bestAction sample.1) hnextAction hbest
          (uniformReferenceThompsonAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
            prior environment bestAction hbestAction n)
          (fun pair : History.FinitePairHistory Action Reward n × Action =>
            score.successor n pair.1 pair.2)
          (score.measurable_successor n))

/-- A selector is mean-optimal when it maximizes the environment-dependent
action mean pointwise.  This contract separates a genuine best-action regret
interpretation from the comparator-relative algebra below. -/
def IsOptimalMeanSelector
    {Env : Type u} {Action : Type v}
    (mean : Env -> Action -> Real) (bestAction : Env -> Action) : Prop :=
  forall env arm, mean env arm <= mean env (bestAction env)

/-- Finite-horizon comparator-relative mean regret.  It is Bayesian
pseudo-regret when `bestAction` satisfies `IsOptimalMeanSelector mean
bestAction` and the environment is integrated against a prior. -/
def trajectoryBayesMeanRegret
    {Env : Type u} {Action : Type v} {Reward : Type w}
    (mean : Env -> Action -> Real) (bestAction : Env -> Action)
    (sample : Env × ((n : Nat) -> Action × Reward)) (horizon : Nat) : Real :=
  ∑ t ∈ range horizon,
    (mean sample.1 (bestAction sample.1) -
      mean sample.1 (environmentTrajectoryAction sample t))

/--
LML-shaped Thompson Bayesian regret decomposition on the locally generated
recursive trajectory.  Integrability is explicit; bounded clipped scores and
bounded action means can discharge these four contracts downstream.
-/
theorem integral_trajectoryBayesMeanRegret_eq_add_historyScore
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (mean : Env -> Action -> Real)
    (score : HistoryActionScore Action Reward)
    (horizon : Nat)
    (hmeanBest : Integrable (fun sample :
      Env × ((n : Nat) -> Action × Reward) =>
        mean sample.1 (bestAction sample.1))
      (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
        (uniformReferenceThompsonAlgorithm
          prior environment bestAction hbestAction) environment))
    (hmeanAction : forall t : Nat, t < horizon -> Integrable (fun sample :
      Env × ((n : Nat) -> Action × Reward) =>
        mean sample.1 (environmentTrajectoryAction sample t))
      (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
        (uniformReferenceThompsonAlgorithm
          prior environment bestAction hbestAction) environment))
    (hscoreAction : forall t : Nat, t < horizon -> Integrable (fun sample :
      Env × ((n : Nat) -> Action × Reward) =>
        trajectoryHistoryScore score sample t)
      (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
        (uniformReferenceThompsonAlgorithm
          prior environment bestAction hbestAction) environment))
    (hscoreBest : forall t : Nat, t < horizon -> Integrable (fun sample :
      Env × ((n : Nat) -> Action × Reward) =>
        trajectoryBestHistoryScore score bestAction sample t)
      (prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel
        (uniformReferenceThompsonAlgorithm
          prior environment bestAction hbestAction) environment)) :
    let algorithm :=
      uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
    let actualMeasure :=
      prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    integral actualMeasure (fun sample =>
        trajectoryBayesMeanRegret mean bestAction sample horizon) =
      integral actualMeasure (fun sample =>
        ∑ t ∈ range horizon,
          (mean sample.1 (bestAction sample.1) -
            trajectoryBestHistoryScore score bestAction sample t)) +
      integral actualMeasure (fun sample =>
        ∑ t ∈ range horizon,
          (trajectoryHistoryScore score sample t -
            mean sample.1 (environmentTrajectoryAction sample t))) := by
  dsimp only
  let algorithm :=
    uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
  let actualMeasure :=
    prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  have hscoreIntegral (t : Nat) :
      integral actualMeasure (fun sample =>
          trajectoryHistoryScore score sample t) =
        integral actualMeasure (fun sample =>
          trajectoryBestHistoryScore score bestAction sample t) := by
    exact uniformReferenceThompsonAlgorithm_integral_historyScore_eq_bestAction
      prior environment bestAction hbestAction score t
  have hregretTerm (t : Nat) (ht : t ∈ range horizon) :
      Integrable (fun sample :
        Env × ((n : Nat) -> Action × Reward) =>
          mean sample.1 (bestAction sample.1) -
            mean sample.1 (environmentTrajectoryAction sample t))
        actualMeasure :=
    hmeanBest.sub (hmeanAction t (mem_range.mp ht))
  have hbestTerm (t : Nat) (ht : t ∈ range horizon) :
      Integrable (fun sample :
        Env × ((n : Nat) -> Action × Reward) =>
          mean sample.1 (bestAction sample.1) -
            trajectoryBestHistoryScore score bestAction sample t)
        actualMeasure :=
    hmeanBest.sub (hscoreBest t (mem_range.mp ht))
  have hactionTerm (t : Nat) (ht : t ∈ range horizon) :
      Integrable (fun sample :
        Env × ((n : Nat) -> Action × Reward) =>
          trajectoryHistoryScore score sample t -
            mean sample.1 (environmentTrajectoryAction sample t))
        actualMeasure :=
    (hscoreAction t (mem_range.mp ht)).sub
      (hmeanAction t (mem_range.mp ht))
  calc
    integral actualMeasure (fun sample =>
        trajectoryBayesMeanRegret mean bestAction sample horizon) =
      ∑ t ∈ range horizon,
        integral actualMeasure (fun sample =>
          mean sample.1 (bestAction sample.1) -
            mean sample.1 (environmentTrajectoryAction sample t)) := by
        simpa only [trajectoryBayesMeanRegret] using
          (ExpectationBochnerSums.integral_finset_sum
            actualMeasure (range horizon)
            (fun t sample =>
              mean sample.1 (bestAction sample.1) -
                mean sample.1 (environmentTrajectoryAction sample t))
            hregretTerm)
    _ = (∑ t ∈ range horizon,
          (integral actualMeasure (fun sample =>
            mean sample.1 (bestAction sample.1)) -
          integral actualMeasure (fun sample =>
            trajectoryBestHistoryScore score bestAction sample t))) +
        ∑ t ∈ range horizon,
          (integral actualMeasure (fun sample =>
            trajectoryHistoryScore score sample t) -
          integral actualMeasure (fun sample =>
            mean sample.1 (environmentTrajectoryAction sample t))) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro t ht
        rw [integral_sub hmeanBest
          (hmeanAction t (mem_range.mp ht))]
        rw [hscoreIntegral t]
        ring
    _ = (∑ t ∈ range horizon,
          integral actualMeasure (fun sample =>
            mean sample.1 (bestAction sample.1) -
              trajectoryBestHistoryScore score bestAction sample t)) +
        ∑ t ∈ range horizon,
          integral actualMeasure (fun sample =>
            trajectoryHistoryScore score sample t -
              mean sample.1 (environmentTrajectoryAction sample t)) := by
        congr 1
        · apply sum_congr rfl
          intro t ht
          rw [integral_sub hmeanBest (hscoreBest t (mem_range.mp ht))]
        · apply sum_congr rfl
          intro t ht
          rw [integral_sub (hscoreAction t (mem_range.mp ht))
            (hmeanAction t (mem_range.mp ht))]
    _ = integral actualMeasure (fun sample =>
          ∑ t ∈ range horizon,
            (mean sample.1 (bestAction sample.1) -
              trajectoryBestHistoryScore score bestAction sample t)) +
        integral actualMeasure (fun sample =>
          ∑ t ∈ range horizon,
            (trajectoryHistoryScore score sample t -
              mean sample.1 (environmentTrajectoryAction sample t))) := by
        rw [ExpectationBochnerSums.integral_finset_sum
          actualMeasure (range horizon)
          (fun t sample =>
            mean sample.1 (bestAction sample.1) -
              trajectoryBestHistoryScore score bestAction sample t)
          hbestTerm]
        rw [ExpectationBochnerSums.integral_finset_sum
          actualMeasure (range horizon)
          (fun t sample =>
            trajectoryHistoryScore score sample t -
              mean sample.1 (environmentTrajectoryAction sample t))
          hactionTerm]

end Thompson
end BanditRLProof
