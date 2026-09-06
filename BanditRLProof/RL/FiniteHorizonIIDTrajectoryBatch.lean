import BanditRLProof.RL.FiniteHorizonEmpiricalModel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# IID generated-trajectory batches for finite-horizon RL

This module maps a finite product of genuine policy trajectory laws into the
finite-batch empirical-model surface.  It exposes both the episode/stage
marginal law and independence across episode coordinates.  The policy is fixed
across episodes; adaptive cross-episode policy updates and concentration of
visit-conditioned empirical ratios remain downstream.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v w

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MDP

/-- Current state immediately before a recorded trajectory action. -/
def trajectoryStateAt (mdp : MDP State Action)
    (trajectory : State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) : State :=
  if hzero : stage.val = 0 then
    trajectory.1
  else
    (trajectory.2 ⟨stage.val - 1, by omega⟩).2

/-- A full generated trajectory viewed as one empirical record at a stage. -/
def episodeStepOfTrajectory (mdp : MDP State Action)
    (trajectory : State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) : EpisodeStep State Action where
  state := mdp.trajectoryStateAt trajectory stage
  action := (trajectory.2 stage).1
  reward := mdp.reward (mdp.trajectoryStateAt trajectory stage)
    (trajectory.2 stage).1
  nextState := (trajectory.2 stage).2

/-- A finite family of full trajectories mapped to empirical episode records. -/
def episodeBatchOfTrajectories (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon) :
    EpisodeBatch mdp episodes :=
  fun episode stage => mdp.episodeStepOfTrajectory (trajectories episode) stage

/-- One trajectory's contribution to a stage/state/action visit count. -/
def trajectoryVisitContribution (mdp : MDP State Action)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (trajectory : State × StepTrace Action State mdp.horizon) : Nat :=
  let step := mdp.episodeStepOfTrajectory trajectory stage
  if step.state = state /\ step.action = action then 1 else 0

/-- One trajectory's contribution to a stage/state/action reward sum. -/
def trajectoryRewardContribution (mdp : MDP State Action)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (trajectory : State × StepTrace Action State mdp.horizon) : Real :=
  let step := mdp.episodeStepOfTrajectory trajectory stage
  if step.state = state /\ step.action = action then step.reward else 0

/-- One trajectory's contribution to a stage/state/action/next-state count. -/
def trajectoryTransitionContribution (mdp : MDP State Action)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State)
    (trajectory : State × StepTrace Action State mdp.horizon) : Nat :=
  let step := mdp.episodeStepOfTrajectory trajectory stage
  if step.state = state /\ step.action = action /\
      step.nextState = nextState then 1 else 0

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- The stage record extracted from a finite trajectory is measurable. -/
theorem measurable_episodeStepOfTrajectory (mdp : MDP State Action)
    (stage : Fin mdp.horizon) :
    Measurable (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage) := by
  exact measurable_of_finite _

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- Mapping a finite trajectory family to its empirical batch is measurable. -/
theorem measurable_episodeBatchOfTrajectories (mdp : MDP State Action)
    (episodes : Nat) :
    Measurable (mdp.episodeBatchOfTrajectories episodes) := by
  exact measurable_of_finite _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
@[simp]
theorem episodeBatchOfTrajectories_apply (mdp : MDP State Action)
    (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon)
    (episode : Fin episodes) (stage : Fin mdp.horizon) :
    mdp.episodeBatchOfTrajectories episodes trajectories episode stage =
      mdp.episodeStepOfTrajectory (trajectories episode) stage :=
  rfl

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Extracted batch visits are exactly the sum of trajectory contributions. -/
theorem episodeBatchOfTrajectories_visitCount (mdp : MDP State Action)
    (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (mdp.episodeBatchOfTrajectories episodes trajectories).visitCount
        stage state action =
      ∑ episode,
        mdp.trajectoryVisitContribution stage state action
          (trajectories episode) := by
  rfl

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Extracted batch rewards are exactly the sum of trajectory contributions. -/
theorem episodeBatchOfTrajectories_rewardSum (mdp : MDP State Action)
    (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (mdp.episodeBatchOfTrajectories episodes trajectories).rewardSum
        stage state action =
      ∑ episode,
        mdp.trajectoryRewardContribution stage state action
          (trajectories episode) := by
  rfl

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Extracted transition counts are exactly trajectory-indicator sums. -/
theorem episodeBatchOfTrajectories_transitionCount (mdp : MDP State Action)
    (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    (mdp.episodeBatchOfTrajectories episodes trajectories).transitionCount
        stage state action nextState =
      ∑ episode,
        mdp.trajectoryTransitionContribution stage state action nextState
          (trajectories episode) := by
  rfl

omit [Nonempty State] [Nonempty Action] in
/-- A fixed visit contribution is measurable on the generated trajectory. -/
theorem measurable_trajectoryVisitContribution (mdp : MDP State Action)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    Measurable (mdp.trajectoryVisitContribution stage state action) := by
  exact measurable_of_finite _

omit [Nonempty State] [Nonempty Action] in
/-- A fixed reward contribution is measurable on the generated trajectory. -/
theorem measurable_trajectoryRewardContribution (mdp : MDP State Action)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    Measurable (mdp.trajectoryRewardContribution stage state action) := by
  exact measurable_of_finite _

omit [Nonempty State] [Nonempty Action] in
/-- A fixed transition contribution is measurable on the generated trajectory. -/
theorem measurable_trajectoryTransitionContribution (mdp : MDP State Action)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    Measurable
      (mdp.trajectoryTransitionContribution stage state action nextState) := by
  exact measurable_of_finite _

end MDP

namespace MarkovPolicy

/-- Finite iid product of the generated single-episode trajectory law. -/
noncomputable def iidTrajectoryFamilyMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    Measure (Fin episodes -> State × StepTrace Action State mdp.horizon) :=
  Measure.pi fun _episode => policy.trajectoryMeasure initialState

instance instIIDTrajectoryFamilyMeasureIsProbabilityMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    IsProbabilityMeasure
      (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
  unfold iidTrajectoryFamilyMeasure
  infer_instance

/-- Pushforward law of the empirical batch extracted from iid trajectories. -/
noncomputable def iidEpisodeBatchMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) : Measure (EpisodeBatch mdp episodes) :=
  (policy.iidTrajectoryFamilyMeasure initialState episodes).map
    (mdp.episodeBatchOfTrajectories episodes)

instance instIIDEpisodeBatchMeasureIsProbabilityMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    IsProbabilityMeasure (policy.iidEpisodeBatchMeasure initialState episodes) := by
  unfold iidEpisodeBatchMeasure
  exact Measure.isProbabilityMeasure_map
    (mdp.measurable_episodeBatchOfTrajectories episodes).aemeasurable

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every product coordinate has the generated single-episode trajectory law. -/
theorem iidTrajectoryFamilyMeasure_map_eval
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes) :
    (policy.iidTrajectoryFamilyMeasure initialState episodes).map
        (Function.eval episode) =
      policy.trajectoryMeasure initialState := by
  exact
    (MeasureTheory.measurePreserving_eval
      (fun _episode : Fin episodes => policy.trajectoryMeasure initialState)
      episode).map_eq

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/--
Each episode/stage coordinate of the mapped batch has the corresponding
pushforward of the genuine generated single-trajectory law.
-/
theorem iidEpisodeBatchMeasure_map_eval
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes) (stage : Fin mdp.horizon) :
    (policy.iidEpisodeBatchMeasure initialState episodes).map
        (fun batch => batch episode stage) =
      (policy.trajectoryMeasure initialState).map
        (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage) := by
  have hbatch : Measurable (mdp.episodeBatchOfTrajectories episodes) :=
    mdp.measurable_episodeBatchOfTrajectories episodes
  have hbatchEval : Measurable
      (fun batch : EpisodeBatch mdp episodes => batch episode stage) :=
    (measurable_pi_apply stage).comp (measurable_pi_apply episode)
  have htrajectoryEval : Measurable
      (Function.eval episode :
        (Fin episodes -> State × StepTrace Action State mdp.horizon) ->
          State × StepTrace Action State mdp.horizon) :=
    measurable_pi_apply episode
  have hstep : Measurable
      (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage) :=
    mdp.measurable_episodeStepOfTrajectory stage
  unfold iidEpisodeBatchMeasure
  rw [Measure.map_map hbatchEval hbatch]
  rw [show
      (fun batch => batch episode stage) ∘
          mdp.episodeBatchOfTrajectories episodes =
        (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage) ∘
          Function.eval episode by rfl]
  rw [← Measure.map_map hstep htrajectoryEval]
  rw [policy.iidTrajectoryFamilyMeasure_map_eval initialState episode]

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- Stage records from distinct product coordinates are independent. -/
theorem iIndepFun_episodeStepOfTrajectory
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories =>
        mdp.episodeStepOfTrajectory (trajectories episode) stage)
      (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
  unfold iidTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (mdp.measurable_episodeStepOfTrajectory stage).aemeasurable

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- Fixed-stage record coordinates are independent under the mapped batch law. -/
theorem iIndepFun_iidEpisodeBatch_eval
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon) :
    ProbabilityTheory.iIndepFun
      (fun episode (batch : EpisodeBatch mdp episodes) => batch episode stage)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  have hbatch : Measurable (mdp.episodeBatchOfTrajectories episodes) :=
    mdp.measurable_episodeBatchOfTrajectories episodes
  have hbatchCoordinates : Measurable
      (fun batch : EpisodeBatch mdp episodes =>
        fun episode => batch episode stage) :=
    measurable_pi_lambda _ fun episode =>
      (measurable_pi_apply stage).comp (measurable_pi_apply episode)
  have hbatchCoordinate : forall episode : Fin episodes,
      Measurable
        (fun batch : EpisodeBatch mdp episodes => batch episode stage) :=
    fun episode => (measurable_pi_apply stage).comp (measurable_pi_apply episode)
  have hsource :=
    policy.iIndepFun_episodeStepOfTrajectory initialState episodes stage
  have hsourceEq :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun episode =>
        ((mdp.measurable_episodeStepOfTrajectory stage).comp
          (measurable_pi_apply episode)).aemeasurable)).1 hsource
  have hsourceEq' :
      (policy.iidTrajectoryFamilyMeasure initialState episodes).map
          (fun trajectories episode =>
            mdp.episodeStepOfTrajectory (trajectories episode) stage) =
        Measure.pi fun episode =>
          (policy.iidTrajectoryFamilyMeasure initialState episodes).map
            (fun trajectories =>
              mdp.episodeStepOfTrajectory (trajectories episode) stage) := by
    simpa only [Function.comp_apply] using hsourceEq
  apply
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun episode => (hbatchCoordinate episode).aemeasurable)).2
  unfold iidEpisodeBatchMeasure
  rw [Measure.map_map hbatchCoordinates hbatch]
  rw [show
      (fun batch : EpisodeBatch mdp episodes =>
        fun episode => batch episode stage) ∘
          mdp.episodeBatchOfTrajectories episodes =
        (fun trajectories episode =>
          mdp.episodeStepOfTrajectory (trajectories episode) stage) by rfl]
  rw [hsourceEq']
  congr 1
  funext episode
  rw [Measure.map_map (hbatchCoordinate episode) hbatch]
  rfl

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- Measurable fixed-stage batch-record statistics are independent by episode. -/
theorem iIndepFun_iidEpisodeBatch_statistic
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    {Target : Type w} [MeasurableSpace Target]
    (statistic : EpisodeStep State Action -> Target)
    (hstatistic : Measurable statistic) :
    ProbabilityTheory.iIndepFun
      (fun episode (batch : EpisodeBatch mdp episodes) =>
        statistic (batch episode stage))
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  exact
    (policy.iIndepFun_iidEpisodeBatch_eval initialState episodes stage).comp
      (fun _episode => statistic) (fun _episode => hstatistic)

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- Any measurable statistic of a fixed-stage record remains independent by episode. -/
theorem iIndepFun_episodeStatistic
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    {Target : Type w} [MeasurableSpace Target]
    (statistic : EpisodeStep State Action -> Target)
    (hstatistic : Measurable statistic) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories =>
        statistic (mdp.episodeStepOfTrajectory (trajectories episode) stage))
      (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
  unfold iidTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (hstatistic.comp (mdp.measurable_episodeStepOfTrajectory stage)).aemeasurable

omit [Nonempty State] [Nonempty Action] in
/-- Visit-count summands are independent across iid episode trajectories. -/
theorem iIndepFun_trajectoryVisitContribution
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories =>
        mdp.trajectoryVisitContribution stage state action
          (trajectories episode))
      (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
  unfold iidTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (mdp.measurable_trajectoryVisitContribution stage state action).aemeasurable

omit [Nonempty State] [Nonempty Action] in
/-- Reward-sum summands are independent across iid episode trajectories. -/
theorem iIndepFun_trajectoryRewardContribution
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories =>
        mdp.trajectoryRewardContribution stage state action
          (trajectories episode))
      (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
  unfold iidTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (mdp.measurable_trajectoryRewardContribution stage state action).aemeasurable

omit [Nonempty State] [Nonempty Action] in
/-- Transition-count summands are independent across iid episode trajectories. -/
theorem iIndepFun_trajectoryTransitionContribution
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (nextState : State) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories =>
        mdp.trajectoryTransitionContribution stage state action nextState
          (trajectories episode))
      (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
  unfold iidTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (mdp.measurable_trajectoryTransitionContribution
      stage state action nextState).aemeasurable

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/--
Route endpoint: generated batch coordinates have the correct marginal law and
are independent across episodes at every fixed stage.
-/
theorem iidEpisodeBatch_stepLaw_and_independence
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon) :
    (forall episode : Fin episodes,
      (policy.iidEpisodeBatchMeasure initialState episodes).map
          (fun batch => batch episode stage) =
        (policy.trajectoryMeasure initialState).map
          (fun trajectory => mdp.episodeStepOfTrajectory trajectory stage)) /\
      ProbabilityTheory.iIndepFun
        (fun episode (batch : EpisodeBatch mdp episodes) =>
          batch episode stage)
        (policy.iidEpisodeBatchMeasure initialState episodes) := by
  exact ⟨fun episode =>
    policy.iidEpisodeBatchMeasure_map_eval initialState episode stage,
    policy.iIndepFun_iidEpisodeBatch_eval initialState episodes stage⟩

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
