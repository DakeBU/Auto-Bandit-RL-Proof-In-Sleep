import BanditRLProof.RL.FiniteHorizonIIDTrajectoryBatch
import BanditRLProof.ConcentrationSubGaussian

/-!
# IID fixed-coordinate count concentration for finite-horizon RL

This module applies the Mathlib-backed bounded-variable Hoeffding route to the
fixed-policy iid episode-batch law. It proves two-sided confidence tails for
one visit coordinate and one transition coordinate. Simultaneous finite
coordinate events, random-denominator ratios, and adaptive episode policies
remain downstream.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace EpisodeStep

/-- Real indicator that one record visits a fixed state-action coordinate. -/
def visitIndicator (state : State) (action : Action)
    (step : EpisodeStep State Action) : Real :=
  if step.state = state /\ step.action = action then 1 else 0

/-- Real indicator that one record realizes a fixed transition coordinate. -/
def transitionIndicator (state : State) (action : Action) (nextState : State)
    (step : EpisodeStep State Action) : Real :=
  if step.state = state /\ step.action = action /\
      step.nextState = nextState then 1 else 0

omit [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] in
/-- A fixed visit indicator is measurable on empirical records. -/
theorem measurable_visitIndicator (state : State) (action : Action) :
    Measurable (visitIndicator state action) := by
  unfold visitIndicator
  refine Measurable.ite ?_ measurable_const measurable_const
  exact
    (measurable_state (measurableSet_singleton state)).inter
      (measurable_action (measurableSet_singleton action))

omit [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] in
/-- A fixed transition indicator is measurable on empirical records. -/
theorem measurable_transitionIndicator
    (state : State) (action : Action) (nextState : State) :
    Measurable (transitionIndicator state action nextState) := by
  unfold transitionIndicator
  refine Measurable.ite ?_ measurable_const measurable_const
  exact
    (measurable_state (measurableSet_singleton state)).inter
      ((measurable_action (measurableSet_singleton action)).inter
        (measurable_nextState (measurableSet_singleton nextState)))

omit [MeasurableSpace State] [MeasurableSpace Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] in
/-- Every visit indicator lies in the Hoeffding interval `[0,1]`. -/
theorem visitIndicator_mem_Icc (state : State) (action : Action)
    (step : EpisodeStep State Action) :
    visitIndicator state action step ∈ Set.Icc (0 : Real) 1 := by
  by_cases h : step.state = state /\ step.action = action <;>
    simp [visitIndicator, h]

omit [MeasurableSpace State] [MeasurableSpace Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] in
/-- Every transition indicator lies in the Hoeffding interval `[0,1]`. -/
theorem transitionIndicator_mem_Icc
    (state : State) (action : Action) (nextState : State)
    (step : EpisodeStep State Action) :
    transitionIndicator state action nextState step ∈ Set.Icc (0 : Real) 1 := by
  by_cases h : step.state = state /\ step.action = action /\
      step.nextState = nextState <;>
    simp [transitionIndicator, h]

end EpisodeStep

namespace MarkovPolicy

/-- Genuine single-trajectory mean of a fixed stage/state/action visit indicator. -/
noncomputable def stageVisitProbability
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action) : Real :=
  integral (policy.trajectoryMeasure initialState) fun trajectory =>
    EpisodeStep.visitIndicator state action
      (mdp.episodeStepOfTrajectory trajectory stage)

/--
Genuine single-trajectory joint probability of a fixed
`(state, action, nextState)` coordinate. This is not a conditional transition
probability given the current state and action.
-/
noncomputable def stageTransitionJointProbability
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) : Real :=
  integral (policy.trajectoryMeasure initialState) fun trajectory =>
    EpisodeStep.transitionIndicator state action nextState
      (mdp.episodeStepOfTrajectory trajectory stage)

omit [Nonempty State] [Nonempty Action] in
/-- A stage visit mean is the real mass of its measurable trajectory event. -/
theorem stageVisitProbability_eq_measureReal
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    policy.stageVisitProbability initialState stage state action =
      (policy.trajectoryMeasure initialState).real
        {trajectory |
          (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
            (mdp.episodeStepOfTrajectory trajectory stage).action = action} := by
  have hstep := mdp.measurable_episodeStepOfTrajectory stage
  have hset : MeasurableSet
      {trajectory |
        (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
          (mdp.episodeStepOfTrajectory trajectory stage).action = action} :=
    (hstep (EpisodeStep.measurable_state (measurableSet_singleton state))).inter
      (hstep (EpisodeStep.measurable_action (measurableSet_singleton action)))
  rw [stageVisitProbability, ← integral_indicator_one hset]
  refine integral_congr_ae (Filter.Eventually.of_forall fun trajectory => ?_)
  by_cases h :
      (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
        (mdp.episodeStepOfTrajectory trajectory stage).action = action <;>
    simp [EpisodeStep.visitIndicator, Set.indicator, h]

omit [Nonempty State] [Nonempty Action] in
/-- A stage joint-transition mean is the real mass of its measurable event. -/
theorem stageTransitionJointProbability_eq_measureReal
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    policy.stageTransitionJointProbability initialState stage state action nextState =
      (policy.trajectoryMeasure initialState).real
        {trajectory |
          (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
            (mdp.episodeStepOfTrajectory trajectory stage).action = action /\
              (mdp.episodeStepOfTrajectory trajectory stage).nextState = nextState} := by
  have hstep := mdp.measurable_episodeStepOfTrajectory stage
  have hset : MeasurableSet
      {trajectory |
        (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
          (mdp.episodeStepOfTrajectory trajectory stage).action = action /\
            (mdp.episodeStepOfTrajectory trajectory stage).nextState = nextState} :=
    (hstep (EpisodeStep.measurable_state (measurableSet_singleton state))).inter
      ((hstep (EpisodeStep.measurable_action (measurableSet_singleton action))).inter
        (hstep (EpisodeStep.measurable_nextState
          (measurableSet_singleton nextState))))
  rw [stageTransitionJointProbability, ← integral_indicator_one hset]
  refine integral_congr_ae (Filter.Eventually.of_forall fun trajectory => ?_)
  by_cases h :
      (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
        (mdp.episodeStepOfTrajectory trajectory stage).action = action /\
          (mdp.episodeStepOfTrajectory trajectory stage).nextState = nextState <;>
    simp [EpisodeStep.transitionIndicator, Set.indicator, h]

omit [Nonempty State] [Nonempty Action] in
/-- Every genuine stage visit probability lies in `[0,1]`. -/
theorem stageVisitProbability_mem_Icc
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    policy.stageVisitProbability initialState stage state action ∈ Set.Icc (0 : Real) 1 := by
  rw [policy.stageVisitProbability_eq_measureReal initialState stage state action]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

omit [Nonempty State] [Nonempty Action] in
/-- Every genuine stage joint-transition probability lies in `[0,1]`. -/
theorem stageTransitionJointProbability_mem_Icc
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    policy.stageTransitionJointProbability initialState stage state action nextState ∈
      Set.Icc (0 : Real) 1 := by
  rw [policy.stageTransitionJointProbability_eq_measureReal
    initialState stage state action nextState]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

omit [Nonempty State] [Nonempty Action] in
/-- A fixed joint-transition probability is bounded by its visit probability. -/
theorem stageTransitionJointProbability_le_stageVisitProbability
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    policy.stageTransitionJointProbability initialState stage state action nextState ≤
      policy.stageVisitProbability initialState stage state action := by
  rw [policy.stageTransitionJointProbability_eq_measureReal
      initialState stage state action nextState,
    policy.stageVisitProbability_eq_measureReal initialState stage state action]
  exact measureReal_mono fun _trajectory htrajectory =>
    ⟨htrajectory.1, htrajectory.2.1⟩

omit [Nonempty State] [Nonempty Action] in
/-- Every mapped episode coordinate has the common genuine visit-indicator mean. -/
theorem integral_visitIndicator_iidEpisodeBatchMeasure_eval
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    integral (policy.iidEpisodeBatchMeasure initialState episodes)
        (fun batch => EpisodeStep.visitIndicator state action
          (batch episode stage)) =
      policy.stageVisitProbability initialState stage state action := by
  have heval : Measurable
      (fun batch : EpisodeBatch mdp episodes => batch episode stage) :=
    (measurable_pi_apply stage).comp (measurable_pi_apply episode)
  have hstep : Measurable
      (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage) :=
    mdp.measurable_episodeStepOfTrajectory stage
  have hindicator := EpisodeStep.measurable_visitIndicator state action
  calc
    integral (policy.iidEpisodeBatchMeasure initialState episodes)
        (fun batch => EpisodeStep.visitIndicator state action
          (batch episode stage)) =
      integral
        ((policy.iidEpisodeBatchMeasure initialState episodes).map
          (fun batch => batch episode stage))
        (EpisodeStep.visitIndicator state action) := by
          rw [integral_map heval.aemeasurable hindicator.aestronglyMeasurable]
    _ = integral
        ((policy.trajectoryMeasure initialState).map
          (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage))
        (EpisodeStep.visitIndicator state action) := by
          rw [policy.iidEpisodeBatchMeasure_map_eval initialState episode stage]
    _ = policy.stageVisitProbability initialState stage state action := by
          rw [integral_map hstep.aemeasurable hindicator.aestronglyMeasurable]
          rfl

omit [Nonempty State] [Nonempty Action] in
/-- Every mapped episode coordinate has the common genuine transition-indicator mean. -/
theorem integral_transitionIndicator_iidEpisodeBatchMeasure_eval
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (nextState : State) :
    integral (policy.iidEpisodeBatchMeasure initialState episodes)
        (fun batch => EpisodeStep.transitionIndicator state action nextState
          (batch episode stage)) =
      policy.stageTransitionJointProbability initialState stage state action nextState := by
  have heval : Measurable
      (fun batch : EpisodeBatch mdp episodes => batch episode stage) :=
    (measurable_pi_apply stage).comp (measurable_pi_apply episode)
  have hstep : Measurable
      (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage) :=
    mdp.measurable_episodeStepOfTrajectory stage
  have hindicator :=
    EpisodeStep.measurable_transitionIndicator state action nextState
  calc
    integral (policy.iidEpisodeBatchMeasure initialState episodes)
        (fun batch => EpisodeStep.transitionIndicator state action nextState
          (batch episode stage)) =
      integral
        ((policy.iidEpisodeBatchMeasure initialState episodes).map
          (fun batch => batch episode stage))
        (EpisodeStep.transitionIndicator state action nextState) := by
          rw [integral_map heval.aemeasurable hindicator.aestronglyMeasurable]
    _ = integral
        ((policy.trajectoryMeasure initialState).map
          (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage))
        (EpisodeStep.transitionIndicator state action nextState) := by
          rw [policy.iidEpisodeBatchMeasure_map_eval initialState episode stage]
    _ = policy.stageTransitionJointProbability initialState stage state action nextState := by
          rw [integral_map hstep.aemeasurable hindicator.aestronglyMeasurable]
          rfl

/-- Centered visit indicator for one episode coordinate of a mapped batch. -/
noncomputable def centeredVisitIndicator
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (stage : Fin mdp.horizon) (state : State) (action : Action)
    (episode : Fin episodes) (batch : EpisodeBatch mdp episodes) : Real :=
  EpisodeStep.visitIndicator state action (batch episode stage) -
    policy.stageVisitProbability initialState stage state action

/-- Centered transition indicator for one episode coordinate of a mapped batch. -/
noncomputable def centeredTransitionIndicator
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) (episode : Fin episodes)
    (batch : EpisodeBatch mdp episodes) : Real :=
  EpisodeStep.transitionIndicator state action nextState (batch episode stage) -
    policy.stageTransitionJointProbability initialState stage state action nextState

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The named visit count is the Real sum of mapped record indicators. -/
theorem sum_visitIndicator_eq_cast_visitCount
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    (∑ episode : Fin episodes,
      EpisodeStep.visitIndicator state action (batch episode stage)) =
      (batch.visitCount stage state action : Real) := by
  simp [EpisodeBatch.visitCount, EpisodeStep.visitIndicator]

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The named transition count is the Real sum of mapped record indicators. -/
theorem sum_transitionIndicator_eq_cast_transitionCount
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (nextState : State) :
    (∑ episode : Fin episodes,
      EpisodeStep.transitionIndicator state action nextState
        (batch episode stage)) =
      (batch.transitionCount stage state action nextState : Real) := by
  simp [EpisodeBatch.transitionCount, EpisodeStep.transitionIndicator]

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Centered visit-indicator sums are exactly count minus episode-count times mean. -/
theorem sum_centeredVisitIndicator_eq_cast_visitCount_sub
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (batch : EpisodeBatch mdp episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (∑ episode : Fin episodes,
      policy.centeredVisitIndicator initialState stage state action episode batch) =
      (batch.visitCount stage state action : Real) -
        (episodes : Real) *
          policy.stageVisitProbability initialState stage state action := by
  rw [show (∑ episode : Fin episodes,
      policy.centeredVisitIndicator initialState stage state action episode batch) =
      (∑ episode : Fin episodes,
        EpisodeStep.visitIndicator state action (batch episode stage)) -
        (∑ _episode : Fin episodes,
          policy.stageVisitProbability initialState stage state action) by
    simp only [centeredVisitIndicator, Finset.sum_sub_distrib]]
  rw [sum_visitIndicator_eq_cast_visitCount]
  simp

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Centered transition-indicator sums are count minus episode-count times mean. -/
theorem sum_centeredTransitionIndicator_eq_cast_transitionCount_sub
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (batch : EpisodeBatch mdp episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    (∑ episode : Fin episodes,
      policy.centeredTransitionIndicator initialState stage state action
        nextState episode batch) =
      (batch.transitionCount stage state action nextState : Real) -
        (episodes : Real) *
          policy.stageTransitionJointProbability initialState stage state action nextState := by
  rw [show (∑ episode : Fin episodes,
      policy.centeredTransitionIndicator initialState stage state action
        nextState episode batch) =
      (∑ episode : Fin episodes,
        EpisodeStep.transitionIndicator state action nextState
          (batch episode stage)) -
        (∑ _episode : Fin episodes,
          policy.stageTransitionJointProbability initialState stage state action nextState) by
    simp only [centeredTransitionIndicator, Finset.sum_sub_distrib]]
  rw [sum_transitionIndicator_eq_cast_transitionCount]
  simp

omit [Nonempty State] [Nonempty Action] in
/-- A fixed visit count, coerced to `Real`, is measurable on episode batches. -/
theorem measurable_cast_visitCount
    {mdp : MDP State Action} {episodes : Nat}
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      (batch.visitCount stage state action : Real) := by
  have hsum : Measurable fun batch : EpisodeBatch mdp episodes =>
      ∑ episode : Fin episodes,
        EpisodeStep.visitIndicator state action (batch episode stage) := by
    refine Finset.measurable_sum Finset.univ fun episode _ => ?_
    exact (EpisodeStep.measurable_visitIndicator state action).comp
      ((measurable_pi_apply stage).comp (measurable_pi_apply episode))
  simpa only [sum_visitIndicator_eq_cast_visitCount] using hsum

omit [Nonempty State] [Nonempty Action] in
/-- A fixed transition count, coerced to `Real`, is measurable on episode batches. -/
theorem measurable_cast_transitionCount
    {mdp : MDP State Action} {episodes : Nat}
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      (batch.transitionCount stage state action nextState : Real) := by
  have hsum : Measurable fun batch : EpisodeBatch mdp episodes =>
      ∑ episode : Fin episodes,
        EpisodeStep.transitionIndicator state action nextState
          (batch episode stage) := by
    refine Finset.measurable_sum Finset.univ fun episode _ => ?_
    exact (EpisodeStep.measurable_transitionIndicator state action nextState).comp
      ((measurable_pi_apply stage).comp (measurable_pi_apply episode))
  simpa only [sum_transitionIndicator_eq_cast_transitionCount] using hsum

omit [Nonempty State] [Nonempty Action] in
/-- The fixed visit-count deviation from its genuine mean is measurable. -/
theorem measurable_visitCountDeviation
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      (batch.visitCount stage state action : Real) -
        (episodes : Real) *
          policy.stageVisitProbability initialState stage state action :=
  (measurable_cast_visitCount stage state action).sub measurable_const

omit [Nonempty State] [Nonempty Action] in
/-- The fixed joint-transition-count deviation from its genuine mean is measurable. -/
theorem measurable_transitionCountDeviation
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (stage : Fin mdp.horizon)
    (state : State) (action : Action) (nextState : State) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      (batch.transitionCount stage state action nextState : Real) -
        (episodes : Real) *
          policy.stageTransitionJointProbability initialState stage state action nextState :=
  (measurable_cast_transitionCount stage state action nextState).sub measurable_const

/-- Total Hoeffding variance proxy for a finite iid family of `[0,1]` indicators. -/
noncomputable def iidBernoulliVarianceProxy (episodes : Nat) : NNReal :=
  ∑ _episode : Fin episodes, Concentration.intervalVarianceProxy 0 1

/-- The iid Bernoulli Hoeffding proxy is exactly one quarter per episode. -/
theorem iidBernoulliVarianceProxy_eq (episodes : Nat) :
    iidBernoulliVarianceProxy episodes = (episodes : NNReal) / 4 := by
  simp [iidBernoulliVarianceProxy, Concentration.intervalVarianceProxy]
  norm_num [div_eq_mul_inv]

/-- A positive episode count gives a positive total Bernoulli variance proxy. -/
theorem iidBernoulliVarianceProxy_pos {episodes : Nat} (hepisodes : 0 < episodes) :
    0 < ((iidBernoulliVarianceProxy episodes : NNReal) : Real) := by
  have hsingle : 0 < Concentration.intervalVarianceProxy 0 1 := by
    rw [Concentration.intervalVarianceProxy]
    norm_num
  have hsum : 0 < iidBernoulliVarianceProxy episodes := by
    unfold iidBernoulliVarianceProxy
    refine Finset.sum_pos' (fun _episode _ => zero_le _) ?_
    let episode : Fin episodes := ⟨0, hepisodes⟩
    exact ⟨episode, Finset.mem_univ episode, hsingle⟩
  exact_mod_cast hsum

omit [Nonempty State] [Nonempty Action] in
/-- One centered visit coordinate has the `[0,1]` Hoeffding MGF proxy. -/
theorem centeredVisitIndicator_hasSubgaussianMGF
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (stage : Fin mdp.horizon) (state : State) (action : Action)
    (episode : Fin episodes) :
    ProbabilityTheory.HasSubgaussianMGF
      (policy.centeredVisitIndicator initialState stage state action episode)
      (Concentration.intervalVarianceProxy 0 1)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  have hmeas : AEMeasurable
      (fun batch : EpisodeBatch mdp episodes =>
        EpisodeStep.visitIndicator state action (batch episode stage))
      (policy.iidEpisodeBatchMeasure initialState episodes) :=
    ((EpisodeStep.measurable_visitIndicator state action).comp
      ((measurable_pi_apply stage).comp
        (measurable_pi_apply episode))).aemeasurable
  have hbound : ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
      EpisodeStep.visitIndicator state action (batch episode stage) ∈
        Set.Icc (0 : Real) 1 :=
    Filter.Eventually.of_forall fun batch =>
      EpisodeStep.visitIndicator_mem_Icc state action (batch episode stage)
  have hmean :=
    policy.integral_visitIndicator_iidEpisodeBatchMeasure_eval
      initialState episode stage state action
  simpa [centeredVisitIndicator] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (policy.iidEpisodeBatchMeasure initialState episodes)
      hmeas hbound hmean)

omit [Nonempty State] [Nonempty Action] in
/-- One centered transition coordinate has the `[0,1]` Hoeffding MGF proxy. -/
theorem centeredTransitionIndicator_hasSubgaussianMGF
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) (episode : Fin episodes) :
    ProbabilityTheory.HasSubgaussianMGF
      (policy.centeredTransitionIndicator initialState stage state action
        nextState episode)
      (Concentration.intervalVarianceProxy 0 1)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  have hmeas : AEMeasurable
      (fun batch : EpisodeBatch mdp episodes =>
        EpisodeStep.transitionIndicator state action nextState
          (batch episode stage))
      (policy.iidEpisodeBatchMeasure initialState episodes) :=
    ((EpisodeStep.measurable_transitionIndicator state action nextState).comp
      ((measurable_pi_apply stage).comp
        (measurable_pi_apply episode))).aemeasurable
  have hbound : ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
      EpisodeStep.transitionIndicator state action nextState
          (batch episode stage) ∈ Set.Icc (0 : Real) 1 :=
    Filter.Eventually.of_forall fun batch =>
      EpisodeStep.transitionIndicator_mem_Icc
        state action nextState (batch episode stage)
  have hmean :=
    policy.integral_transitionIndicator_iidEpisodeBatchMeasure_eval
      initialState episode stage state action nextState
  simpa [centeredTransitionIndicator] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (policy.iidEpisodeBatchMeasure initialState episodes)
      hmeas hbound hmean)

omit [Nonempty State] [Nonempty Action] in
/-- Centered visit coordinates remain independent under the mapped batch law. -/
theorem iIndepFun_centeredVisitIndicator
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    ProbabilityTheory.iIndepFun
      (policy.centeredVisitIndicator initialState stage state action)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  simpa [centeredVisitIndicator] using
    policy.iIndepFun_iidEpisodeBatch_statistic initialState episodes stage
      (fun step => EpisodeStep.visitIndicator state action step -
        policy.stageVisitProbability initialState stage state action)
      ((EpisodeStep.measurable_visitIndicator state action).sub measurable_const)

omit [Nonempty State] [Nonempty Action] in
/-- Centered transition coordinates remain independent under the mapped batch law. -/
theorem iIndepFun_centeredTransitionIndicator
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (nextState : State) :
    ProbabilityTheory.iIndepFun
      (policy.centeredTransitionIndicator initialState stage state action nextState)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  simpa [centeredTransitionIndicator] using
    policy.iIndepFun_iidEpisodeBatch_statistic initialState episodes stage
      (fun step => EpisodeStep.transitionIndicator state action nextState step -
        policy.stageTransitionJointProbability initialState stage state action nextState)
      ((EpisodeStep.measurable_transitionIndicator state action nextState).sub
        measurable_const)

omit [Nonempty State] [Nonempty Action] in
/-- The fixed visit-count two-sided bad event is measurable. -/
theorem measurableSet_visitCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (delta : Real) :
    MeasurableSet
      {batch : EpisodeBatch mdp episodes |
        Concentration.subGaussianSumConfidenceRadius
            (iidBernoulliVarianceProxy episodes) delta ≤
          |(batch.visitCount stage state action : Real) -
            (episodes : Real) *
              policy.stageVisitProbability initialState stage state action|} :=
  measurableSet_le measurable_const
    (policy.measurable_visitCountDeviation initialState stage state action).abs

omit [Nonempty State] [Nonempty Action] in
/-- The fixed joint-transition-count two-sided bad event is measurable. -/
theorem measurableSet_transitionCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (nextState : State) (delta : Real) :
    MeasurableSet
      {batch : EpisodeBatch mdp episodes |
        Concentration.subGaussianSumConfidenceRadius
            (iidBernoulliVarianceProxy episodes) delta ≤
          |(batch.transitionCount stage state action nextState : Real) -
            (episodes : Real) *
              policy.stageTransitionJointProbability initialState stage state action
                nextState|} :=
  measurableSet_le measurable_const
    (policy.measurable_transitionCountDeviation
      initialState stage state action nextState).abs

omit [Nonempty State] [Nonempty Action] in
/--
Two-sided delta confidence tail for one fixed visit-count coordinate under the
mapped fixed-policy iid episode-batch law.
-/
theorem iidEpisodeBatch_visitCount_abs_tail_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (policy.iidEpisodeBatchMeasure initialState episodes)
        {batch |
          Concentration.subGaussianSumConfidenceRadius
              (iidBernoulliVarianceProxy episodes) delta <=
            |(batch.visitCount stage state action : Real) -
              (episodes : Real) *
                policy.stageVisitProbability initialState stage state action|} <=
      ENNReal.ofReal delta := by
  have htail :=
    Concentration.subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun
      (policy.iidEpisodeBatchMeasure initialState episodes)
      (policy.iIndepFun_centeredVisitIndicator
        initialState episodes stage state action)
      (s := Finset.univ)
      (c := fun _episode : Fin episodes =>
        Concentration.intervalVarianceProxy 0 1)
      (fun episode _ =>
        policy.centeredVisitIndicator_hasSubgaussianMGF
          initialState stage state action episode)
      (iidBernoulliVarianceProxy_pos hepisodes)
      delta hdelta hdelta_le_one
  simpa only [iidBernoulliVarianceProxy,
    policy.sum_centeredVisitIndicator_eq_cast_visitCount_sub] using htail

omit [Nonempty State] [Nonempty Action] in
/--
Two-sided delta confidence tail for one fixed transition-count coordinate
under the mapped fixed-policy iid episode-batch law.
-/
theorem iidEpisodeBatch_transitionCount_abs_tail_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (policy.iidEpisodeBatchMeasure initialState episodes)
        {batch |
          Concentration.subGaussianSumConfidenceRadius
              (iidBernoulliVarianceProxy episodes) delta <=
            |(batch.transitionCount stage state action nextState : Real) -
              (episodes : Real) *
                policy.stageTransitionJointProbability initialState stage state action
                  nextState|} <=
      ENNReal.ofReal delta := by
  have htail :=
    Concentration.subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun
      (policy.iidEpisodeBatchMeasure initialState episodes)
      (policy.iIndepFun_centeredTransitionIndicator
        initialState episodes stage state action nextState)
      (s := Finset.univ)
      (c := fun _episode : Fin episodes =>
        Concentration.intervalVarianceProxy 0 1)
      (fun episode _ =>
        policy.centeredTransitionIndicator_hasSubgaussianMGF
          initialState stage state action nextState episode)
      (iidBernoulliVarianceProxy_pos hepisodes)
      delta hdelta hdelta_le_one
  simpa only [iidBernoulliVarianceProxy,
    policy.sum_centeredTransitionIndicator_eq_cast_transitionCount_sub] using htail

omit [Nonempty State] [Nonempty Action] in
/--
Route endpoint: both named fixed-coordinate count tails are available under the
same mapped iid episode-batch law. This conjunction does not union the two bad
events or spend a shared failure budget.
-/
theorem iidEpisodeBatch_visit_and_transition_count_abs_tail_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (policy.iidEpisodeBatchMeasure initialState episodes)
        {batch |
          Concentration.subGaussianSumConfidenceRadius
              (iidBernoulliVarianceProxy episodes) delta <=
            |(batch.visitCount stage state action : Real) -
              (episodes : Real) *
                policy.stageVisitProbability initialState stage state action|} <=
        ENNReal.ofReal delta /\
      (policy.iidEpisodeBatchMeasure initialState episodes)
        {batch |
          Concentration.subGaussianSumConfidenceRadius
              (iidBernoulliVarianceProxy episodes) delta <=
            |(batch.transitionCount stage state action nextState : Real) -
              (episodes : Real) *
                policy.stageTransitionJointProbability initialState stage state action
                  nextState|} <=
        ENNReal.ofReal delta := by
  exact
    ⟨policy.iidEpisodeBatch_visitCount_abs_tail_le
        initialState episodes hepisodes stage state action
        delta hdelta hdelta_le_one,
      policy.iidEpisodeBatch_transitionCount_abs_tail_le
        initialState episodes hepisodes stage state action nextState
        delta hdelta hdelta_le_one⟩

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
