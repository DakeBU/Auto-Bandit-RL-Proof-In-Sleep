import BanditRLProof.RL.FiniteHorizonIIDCountConcentration
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Generated stage-transition joint-law factorization

This module proves that a fixed generated trajectory-stage joint transition
mass factors into its state-action visit mass and the true MDP transition
kernel singleton mass. The proof follows the recursive finite trajectory kernel;
it does not divide by visit probabilities or introduce empirical confidence.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}

namespace StepTrace

def stateAt : {n : Nat} -> State -> StepTrace Action State n -> Fin n -> State
  | 0, _initial, _trace, coordinate => Fin.elim0 coordinate
  | _n + 1, initial, trace, coordinate =>
      Fin.cases initial (fun previous => (trace previous.castSucc).2) coordinate

@[simp]
theorem stateAt_zero (initial : State) (head : Action × State)
    (tail : StepTrace Action State n) :
    stateAt initial (Fin.cons head tail) (0 : Fin (n + 1)) = initial := by
  simp [stateAt]

@[simp]
theorem stateAt_zero_apply (initial : State)
    (trace : StepTrace Action State (n + 1)) :
    stateAt initial trace (0 : Fin (n + 1)) = initial := by
  simp [stateAt]

@[simp]
theorem stateAt_succ (initial : State) (head : Action × State)
    (tail : StepTrace Action State n) (coordinate : Fin n) :
    stateAt initial (Fin.cons head tail) coordinate.succ =
      stateAt head.2 tail coordinate := by
  cases n with
  | zero => exact Fin.elim0 coordinate
  | succ n =>
      refine Fin.cases ?_ (fun previous => ?_) coordinate
      · rfl
      · rfl

theorem stateAt_eq_if {n : Nat} (initial : State)
    (trace : StepTrace Action State n) (coordinate : Fin n) :
    stateAt initial trace coordinate =
      if _hzero : coordinate.val = 0 then initial
      else (trace ⟨coordinate.val - 1, by omega⟩).2 := by
  cases n with
  | zero => exact Fin.elim0 coordinate
  | succ n =>
      refine Fin.cases ?_ (fun previous => ?_) coordinate
      · simp [stateAt]
      · simp only [stateAt, Fin.cases_succ, Fin.val_succ, Nat.succ_ne_zero,
          ↓reduceDIte, Nat.succ_sub_one]
        congr 2

def stateActionAt {n : Nat} (initial : State)
    (trace : StepTrace Action State n) (coordinate : Fin n) : State × Action :=
  (stateAt initial trace coordinate, (trace coordinate).1)

def stateActionNextAt {n : Nat} (initial : State)
    (trace : StepTrace Action State n) (coordinate : Fin n) :
    (State × Action) × State :=
  (stateActionAt initial trace coordinate, (trace coordinate).2)

@[simp]
theorem stateActionAt_cons_succ (initial : State) (head : Action × State)
    (tail : StepTrace Action State n) (coordinate : Fin n) :
    stateActionAt initial (Fin.cons head tail) coordinate.succ =
      stateActionAt head.2 tail coordinate := by
  simp [stateActionAt]

@[simp]
theorem stateActionNextAt_cons_succ (initial : State) (head : Action × State)
    (tail : StepTrace Action State n) (coordinate : Fin n) :
    stateActionNextAt initial (Fin.cons head tail) coordinate.succ =
      stateActionNextAt head.2 tail coordinate := by
  simp [stateActionNextAt]

variable [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]

theorem measurable_stateActionAt {n : Nat} (initial : State) (coordinate : Fin n) :
    Measurable (fun trace : StepTrace Action State n =>
      stateActionAt initial trace coordinate) :=
  measurable_of_finite _

theorem measurable_stateActionNextAt {n : Nat} (initial : State)
    (coordinate : Fin n) :
    Measurable (fun trace : StepTrace Action State n =>
      stateActionNextAt initial trace coordinate) :=
  measurable_of_finite _

end StepTrace

namespace MDP

variable [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

theorem stepTrace_stateAt_eq_trajectoryStateAt (mdp : MDP State Action)
    (trajectory : State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) :
    StepTrace.stateAt trajectory.1 trajectory.2 stage =
      mdp.trajectoryStateAt trajectory stage := by
  simpa [trajectoryStateAt] using
    (StepTrace.stateAt_eq_if trajectory.1 trajectory.2 stage)

end MDP

namespace MarkovPolicy

variable [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]

theorem actionStateKernel_apply_singleton
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    policy.actionStateKernel stage state {(action, nextState)} =
      policy.actionKernel stage state {action} *
        mdp.transition (state, action) {nextState} := by
  unfold actionStateKernel
  rw [show ({(action, nextState)} : Set (Action × State)) =
      ({action} ×ˢ {nextState}) by ext; simp]
  rw [ProbabilityTheory.Kernel.compProd_apply_prod
    (measurableSet_singleton action) (measurableSet_singleton nextState)]
  simp

omit [MeasurableSingletonClass State] in
theorem actionStateKernel_apply_actionSet
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    policy.actionStateKernel stage state ({action} ×ˢ Set.univ) =
      policy.actionKernel stage state {action} := by
  unfold actionStateKernel
  rw [ProbabilityTheory.Kernel.compProd_apply_prod
    (measurableSet_singleton action) MeasurableSet.univ]
  simp

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
theorem trajectoryKernelRemaining_map_head
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (initial : State) :
    (policy.trajectoryKernelRemaining (remaining + 1) hremaining initial).map
        (fun trace => trace 0) =
      policy.actionStateKernel
        ⟨mdp.horizon - (remaining + 1), by omega⟩ initial := by
  rw [trajectoryKernelRemaining]
  rw [← ProbabilityTheory.Kernel.map_apply _ (measurable_pi_apply 0)]
  rw [← ProbabilityTheory.Kernel.map_comp_right _ (StepTrace.measurable_cons remaining)
    (measurable_pi_apply 0)]
  change (((policy.actionStateKernel _).compProd _).map Prod.fst) initial = _
  rw [← ProbabilityTheory.Kernel.fst_eq]
  rw [ProbabilityTheory.Kernel.fst_compProd]

theorem trajectoryKernelRemaining_transitionEvent_eq_visitEvent_mul
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (initial state : State) (action : Action) (nextState : State)
    (coordinate : Fin remaining) :
    (policy.trajectoryKernelRemaining remaining hremaining initial)
        {trace | StepTrace.stateActionNextAt initial trace coordinate =
          ((state, action), nextState)} =
      (policy.trajectoryKernelRemaining remaining hremaining initial)
          {trace | StepTrace.stateActionAt initial trace coordinate = (state, action)} *
        mdp.transition (state, action) {nextState} := by
  classical
  induction remaining generalizing initial with
  | zero => exact Fin.elim0 coordinate
  | succ remaining ih =>
      refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate
      · by_cases hinitial : initial = state
        · subst initial
          have hhead := policy.trajectoryKernelRemaining_map_head
            remaining hremaining state
          have hsingle : MeasurableSet ({(action, nextState)} : Set (Action × State)) :=
            measurableSet_singleton _
          have hactionSet : MeasurableSet ({action} ×ˢ (Set.univ : Set State)) :=
            (measurableSet_singleton action).prod MeasurableSet.univ
          have hsinglePreimage :
              (fun trace : StepTrace Action State (remaining + 1) => trace 0) ⁻¹'
                  ({(action, nextState)} : Set (Action × State)) =
                {trace | StepTrace.stateActionNextAt state trace 0 =
                  ((state, action), nextState)} := by
            ext trace
            simp [StepTrace.stateActionNextAt, StepTrace.stateActionAt, Prod.ext_iff]
          have hactionPreimage :
              (fun trace : StepTrace Action State (remaining + 1) => trace 0) ⁻¹'
                  ({action} ×ˢ (Set.univ : Set State)) =
                {trace | StepTrace.stateActionAt state trace 0 = (state, action)} := by
            ext trace
            simp [StepTrace.stateActionAt]
          calc
            _ = (policy.trajectoryKernelRemaining (remaining + 1) hremaining state).map
                (fun trace => trace 0) {(action, nextState)} := by
                  rw [Measure.map_apply (measurable_pi_apply 0) hsingle]
                  rw [hsinglePreimage]
            _ = policy.actionStateKernel
                ⟨mdp.horizon - (remaining + 1), by omega⟩ state
                {(action, nextState)} := by rw [hhead]
            _ = policy.actionKernel
                  ⟨mdp.horizon - (remaining + 1), by omega⟩ state {action} *
                mdp.transition (state, action) {nextState} :=
              policy.actionStateKernel_apply_singleton _ _ _ _
            _ = policy.actionStateKernel
                  ⟨mdp.horizon - (remaining + 1), by omega⟩ state
                  ({action} ×ˢ Set.univ) *
                mdp.transition (state, action) {nextState} := by
              rw [policy.actionStateKernel_apply_actionSet]
            _ = (policy.trajectoryKernelRemaining (remaining + 1) hremaining state).map
                  (fun trace => trace 0) ({action} ×ˢ Set.univ) *
                mdp.transition (state, action) {nextState} := by rw [hhead]
            _ = _ := by
              rw [Measure.map_apply (measurable_pi_apply 0) hactionSet]
              rw [hactionPreimage]
        · simp [StepTrace.stateActionNextAt, StepTrace.stateActionAt,
            hinitial]
      · rw [trajectoryKernelRemaining]
        have htransitionSet : MeasurableSet
            {trace : StepTrace Action State (remaining + 1) |
              StepTrace.stateActionNextAt initial trace tailCoordinate.succ =
                ((state, action), nextState)} :=
          (StepTrace.measurable_stateActionNextAt initial tailCoordinate.succ)
            (measurableSet_singleton ((state, action), nextState))
        have hvisitSet : MeasurableSet
            {trace : StepTrace Action State (remaining + 1) |
              StepTrace.stateActionAt initial trace tailCoordinate.succ = (state, action)} :=
          (StepTrace.measurable_stateActionAt initial tailCoordinate.succ)
            (measurableSet_singleton (state, action))
        rw [ProbabilityTheory.Kernel.map_apply' _ (StepTrace.measurable_cons remaining)
          _ htransitionSet]
        rw [ProbabilityTheory.Kernel.map_apply' _ (StepTrace.measurable_cons remaining)
          _ hvisitSet]
        have htransitionPreimage := htransitionSet.preimage
          (StepTrace.measurable_cons remaining)
        have hvisitPreimage := hvisitSet.preimage
          (StepTrace.measurable_cons remaining)
        rw [ProbabilityTheory.Kernel.compProd_apply htransitionPreimage]
        rw [ProbabilityTheory.Kernel.compProd_apply hvisitPreimage]
        simp only [Set.preimage_setOf_eq, StepTrace.stateActionNextAt_cons_succ,
          StepTrace.stateActionAt_cons_succ,
          ProbabilityTheory.Kernel.comap_apply]
        simp_rw [ih (by omega) _ tailCoordinate]
        rw [MeasureTheory.lintegral_mul_const _ (measurable_of_finite _)]

theorem trajectoryMeasure_transitionEvent_eq_visitEvent_mul
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    policy.trajectoryMeasure initialState
        {trajectory | StepTrace.stateActionNextAt trajectory.1 trajectory.2 stage =
          ((state, action), nextState)} =
      policy.trajectoryMeasure initialState
          {trajectory | StepTrace.stateActionAt trajectory.1 trajectory.2 stage =
            (state, action)} *
        mdp.transition (state, action) {nextState} := by
  have htransitionSet : MeasurableSet
      {trajectory : State × StepTrace Action State mdp.horizon |
        StepTrace.stateActionNextAt trajectory.1 trajectory.2 stage =
          ((state, action), nextState)} := by
    exact (measurable_of_finite _)
      (measurableSet_singleton ((state, action), nextState))
  have hvisitSet : MeasurableSet
      {trajectory : State × StepTrace Action State mdp.horizon |
        StepTrace.stateActionAt trajectory.1 trajectory.2 stage =
          (state, action)} := by
    exact (measurable_of_finite _) (measurableSet_singleton (state, action))
  unfold trajectoryMeasure
  rw [Measure.compProd_apply htransitionSet]
  rw [Measure.compProd_apply hvisitSet]
  simp only [Set.preimage_setOf_eq]
  simp_rw [policy.trajectoryKernelRemaining_transitionEvent_eq_visitEvent_mul
    mdp.horizon le_rfl _ state action nextState stage]
  rw [MeasureTheory.lintegral_mul_const _ (measurable_of_finite _)]

theorem stageTransitionJointProbability_eq_stageVisitProbability_mul_transition
    [DecidableEq State] [DecidableEq Action]
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    policy.stageTransitionJointProbability initialState stage state action nextState =
      policy.stageVisitProbability initialState stage state action *
        (mdp.transition (state, action) {nextState}).toReal := by
  rw [policy.stageTransitionJointProbability_eq_measureReal
    initialState stage state action nextState]
  rw [policy.stageVisitProbability_eq_measureReal initialState stage state action]
  have htransitionEvent :
      {trajectory : State × StepTrace Action State mdp.horizon |
        (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
          (mdp.episodeStepOfTrajectory trajectory stage).action = action /\
            (mdp.episodeStepOfTrajectory trajectory stage).nextState = nextState} =
        {trajectory | StepTrace.stateActionNextAt trajectory.1 trajectory.2 stage =
          ((state, action), nextState)} := by
    ext trajectory
    simp [MDP.episodeStepOfTrajectory, StepTrace.stateActionNextAt,
      StepTrace.stateActionAt, mdp.stepTrace_stateAt_eq_trajectoryStateAt,
      Prod.ext_iff, and_assoc]
  have hvisitEvent :
      {trajectory : State × StepTrace Action State mdp.horizon |
        (mdp.episodeStepOfTrajectory trajectory stage).state = state /\
          (mdp.episodeStepOfTrajectory trajectory stage).action = action} =
        {trajectory | StepTrace.stateActionAt trajectory.1 trajectory.2 stage =
          (state, action)} := by
    ext trajectory
    simp [MDP.episodeStepOfTrajectory, StepTrace.stateActionAt,
      mdp.stepTrace_stateAt_eq_trajectoryStateAt, Prod.ext_iff]
  rw [htransitionEvent, hvisitEvent]
  unfold Measure.real
  rw [policy.trajectoryMeasure_transitionEvent_eq_visitEvent_mul
    initialState stage state action nextState]
  exact ENNReal.toReal_mul

end MarkovPolicy

end BanditRLProof.FiniteHorizonRL
