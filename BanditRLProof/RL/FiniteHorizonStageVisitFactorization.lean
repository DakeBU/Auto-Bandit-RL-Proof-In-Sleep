import BanditRLProof.RL.FiniteHorizonStageTransitionJointFactorization

/-!
# Generated stage-visit factorization

This module factors a generated trajectory's stage/state/action visit mass
into the corresponding stage-state mass and the policy action-kernel singleton
mass.  It is a population-law identity only: no reachability, action support,
episode count, concentration, or regret premise is introduced.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]

namespace MDP

/-- Chronological MDP stage represented by one coordinate of a remaining trace. -/
def stageOfRemainingCoordinate (mdp : MDP State Action)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (coordinate : Fin remaining) : Fin mdp.horizon :=
  ⟨mdp.horizon - remaining + coordinate.val, by omega⟩

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
@[simp]
theorem stageOfRemainingCoordinate_succ (mdp : MDP State Action)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (coordinate : Fin remaining) :
    mdp.stageOfRemainingCoordinate (remaining + 1) hremaining coordinate.succ =
      mdp.stageOfRemainingCoordinate remaining (by omega) coordinate := by
  apply Fin.ext
  simp [stageOfRemainingCoordinate]
  omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
@[simp]
theorem stageOfRemainingCoordinate_full (mdp : MDP State Action)
    (stage : Fin mdp.horizon) :
    mdp.stageOfRemainingCoordinate mdp.horizon le_rfl stage = stage := by
  apply Fin.ext
  simp [stageOfRemainingCoordinate]

end MDP

namespace MarkovPolicy

omit [DecidableEq Action] in
/--
Inside a remaining generated trace, a state/action visit factors into the
state event and the action singleton selected by the chronological policy
kernel.
-/
theorem trajectoryKernelRemaining_visitEvent_eq_stateEvent_mul_action
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (initial state : State) (action : Action)
    (coordinate : Fin remaining) :
    (policy.trajectoryKernelRemaining remaining hremaining initial)
        {trace | StepTrace.stateActionAt initial trace coordinate =
          (state, action)} =
      (policy.trajectoryKernelRemaining remaining hremaining initial)
          {trace | StepTrace.stateAt initial trace coordinate = state} *
        policy.actionKernel
          (mdp.stageOfRemainingCoordinate remaining hremaining coordinate)
          state {action} := by
  classical
  induction remaining generalizing initial with
  | zero => exact Fin.elim0 coordinate
  | succ remaining ih =>
      refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate
      · by_cases hinitial : initial = state
        · subst initial
          have hhead := policy.trajectoryKernelRemaining_map_head
            remaining hremaining state
          have hactionSet : MeasurableSet
              ({action} ×ˢ (Set.univ : Set State)) :=
            (measurableSet_singleton action).prod MeasurableSet.univ
          have hactionPreimage :
              (fun trace : StepTrace Action State (remaining + 1) => trace 0) ⁻¹'
                  ({action} ×ˢ (Set.univ : Set State)) =
                {trace | StepTrace.stateActionAt state trace 0 =
                  (state, action)} := by
            ext trace
            simp [StepTrace.stateActionAt]
          calc
            _ = (policy.trajectoryKernelRemaining
                  (remaining + 1) hremaining state).map
                (fun trace => trace 0) ({action} ×ˢ Set.univ) := by
                  rw [Measure.map_apply (measurable_pi_apply 0) hactionSet]
                  rw [hactionPreimage]
            _ = policy.actionStateKernel
                ⟨mdp.horizon - (remaining + 1), by omega⟩ state
                ({action} ×ˢ Set.univ) := by rw [hhead]
            _ = policy.actionKernel
                ⟨mdp.horizon - (remaining + 1), by omega⟩ state {action} :=
              policy.actionStateKernel_apply_actionSet _ _ _
            _ = _ := by
              simp [StepTrace.stateAt, MDP.stageOfRemainingCoordinate]
        · simp [StepTrace.stateActionAt, StepTrace.stateAt, hinitial]
      · rw [mdp.stageOfRemainingCoordinate_succ remaining hremaining tailCoordinate]
        rw [trajectoryKernelRemaining]
        have hvisitSet : MeasurableSet
            {trace : StepTrace Action State (remaining + 1) |
              StepTrace.stateActionAt initial trace tailCoordinate.succ =
                (state, action)} :=
          (StepTrace.measurable_stateActionAt initial tailCoordinate.succ)
            (measurableSet_singleton (state, action))
        have hstateSet : MeasurableSet
            {trace : StepTrace Action State (remaining + 1) |
              StepTrace.stateAt initial trace tailCoordinate.succ = state} :=
          (measurable_of_finite _) (measurableSet_singleton state)
        rw [ProbabilityTheory.Kernel.map_apply' _
          (StepTrace.measurable_cons remaining) _ hvisitSet]
        rw [ProbabilityTheory.Kernel.map_apply' _
          (StepTrace.measurable_cons remaining) _ hstateSet]
        have hvisitPreimage := hvisitSet.preimage
          (StepTrace.measurable_cons remaining)
        have hstatePreimage := hstateSet.preimage
          (StepTrace.measurable_cons remaining)
        rw [ProbabilityTheory.Kernel.compProd_apply hvisitPreimage]
        rw [ProbabilityTheory.Kernel.compProd_apply hstatePreimage]
        simp only [Set.preimage_setOf_eq, StepTrace.stateActionAt_cons_succ,
          StepTrace.stateAt_succ, ProbabilityTheory.Kernel.comap_apply]
        simp_rw [ih (by omega) _ tailCoordinate]
        rw [MeasureTheory.lintegral_mul_const _ (measurable_of_finite _)]

omit [DecidableEq Action] in
/-- The full trajectory visit event factors into its state event and action mass. -/
theorem trajectoryMeasure_visitEvent_eq_stateEvent_mul_action
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    policy.trajectoryMeasure initialState
        {trajectory |
          (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
            (mdp.episodeStepOfTrajectory trajectory stage).action = action} =
      policy.trajectoryMeasure initialState
          {trajectory | mdp.trajectoryStateAt trajectory stage = state} *
        policy.actionKernel stage state {action} := by
  have hvisitEvent :
      {trajectory : State × StepTrace Action State mdp.horizon |
        (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
          (mdp.episodeStepOfTrajectory trajectory stage).action = action} =
        {trajectory | StepTrace.stateActionAt trajectory.1 trajectory.2 stage =
          (state, action)} := by
    ext trajectory
    simp [MDP.episodeStepOfTrajectory, StepTrace.stateActionAt,
      mdp.stepTrace_stateAt_eq_trajectoryStateAt, Prod.ext_iff]
  have hstateEvent :
      {trajectory : State × StepTrace Action State mdp.horizon |
        mdp.trajectoryStateAt trajectory stage = state} =
        {trajectory | StepTrace.stateAt trajectory.1 trajectory.2 stage = state} := by
    ext trajectory
    simp [mdp.stepTrace_stateAt_eq_trajectoryStateAt]
  rw [hvisitEvent, hstateEvent]
  have hvisitSet : MeasurableSet
      {trajectory : State × StepTrace Action State mdp.horizon |
        StepTrace.stateActionAt trajectory.1 trajectory.2 stage =
          (state, action)} :=
    (measurable_of_finite _) (measurableSet_singleton (state, action))
  have hstateSet : MeasurableSet
      {trajectory : State × StepTrace Action State mdp.horizon |
        StepTrace.stateAt trajectory.1 trajectory.2 stage = state} :=
    (measurable_of_finite _) (measurableSet_singleton state)
  unfold trajectoryMeasure
  rw [Measure.compProd_apply hvisitSet]
  rw [Measure.compProd_apply hstateSet]
  simp only [Set.preimage_setOf_eq]
  simp_rw [policy.trajectoryKernelRemaining_visitEvent_eq_stateEvent_mul_action
    mdp.horizon le_rfl _ state action stage]
  simp only [mdp.stageOfRemainingCoordinate_full]
  rw [MeasureTheory.lintegral_mul_const _ (measurable_of_finite _)]

/-- Genuine state probability at one chronological stage of a generated trajectory. -/
noncomputable def stageStateProbability
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) : Real :=
  (policy.trajectoryMeasure initialState).real
    {trajectory | mdp.trajectoryStateAt trajectory stage = state}

/-- A generated state/action visit probability is state mass times action mass. -/
theorem stageVisitProbability_eq_stageStateProbability_mul_action
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    policy.stageVisitProbability initialState stage state action =
      policy.stageStateProbability initialState stage state *
        (policy.actionKernel stage state {action}).toReal := by
  rw [policy.stageVisitProbability_eq_measureReal initialState stage state action]
  rw [stageStateProbability]
  unfold Measure.real
  rw [policy.trajectoryMeasure_visitEvent_eq_stateEvent_mul_action
    initialState stage state action]
  exact ENNReal.toReal_mul

end MarkovPolicy

end BanditRLProof.FiniteHorizonRL
