import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIClippedPlanner
import BanditRLProof.RL.FiniteHorizonStageTransitionJointFactorization
import BanditRLProof.ConcentrationFixedMGF
import BanditRLProof.ConcentrationSubGaussian

/-!
# Same-source transition residuals for recurrent UCBVI

This module starts the statistical producer on the actual finite episode law.
For a fixed state/action/next-state coordinate, the residual at a generated
stage is

`1{X=x,A=a} * (1{Y=y} - P(y | x,a))`.

The fixed-tilt exponential budget is charged only when `(x,a)` is really
visited.  Thus the compensator is the generated visit count, rather than the
episode number or an offline reachability proxy.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MDP

/-- One transition-coordinate residual on a chronological trace head. -/
def transitionResidualHead (mdp : MDP State Action)
    (targetState : State) (targetAction : Action) (targetNextState : State)
    (currentState : State) (head : Action × State) : Real :=
  if currentState = targetState ∧ head.1 = targetAction then
    (if head.2 = targetNextState then 1 else 0) -
      (mdp.transition (targetState, targetAction)).real {targetNextState}
  else 0

/-- The realized visit charged by one transition-coordinate residual. -/
def transitionVisitHead (_mdp : MDP State Action)
    (targetState : State) (targetAction : Action)
    (currentState : State) (head : Action × State) : Real :=
  if currentState = targetState ∧ head.1 = targetAction then 1 else 0

/-- Sum of one fixed transition residual over the remaining generated trace. -/
def transitionResidualFrom (mdp : MDP State Action)
    (targetState : State) (targetAction : Action) (targetNextState : State) :
    (remaining : Nat) -> State -> StepTrace Action State remaining -> Real
  | 0, _currentState, _trace => 0
  | remaining + 1, currentState, trace =>
      mdp.transitionResidualHead targetState targetAction targetNextState
          currentState (trace 0) +
        mdp.transitionResidualFrom targetState targetAction targetNextState
          remaining (trace 0).2 (Fin.tail trace)

/-- Sum of actual visits to one state-action coordinate over the remaining trace. -/
def transitionVisitFrom (mdp : MDP State Action)
    (targetState : State) (targetAction : Action) :
    (remaining : Nat) -> State -> StepTrace Action State remaining -> Real
  | 0, _currentState, _trace => 0
  | remaining + 1, currentState, trace =>
      mdp.transitionVisitHead targetState targetAction currentState (trace 0) +
        mdp.transitionVisitFrom targetState targetAction
          remaining (trace 0).2 (Fin.tail trace)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_transitionResidualFrom
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (targetNextState : State) (remaining : Nat) :
    Measurable (fun p : State × StepTrace Action State remaining =>
      mdp.transitionResidualFrom targetState targetAction targetNextState
        remaining p.1 p.2) := by
  exact measurable_of_finite _

omit [Nonempty State] [Nonempty Action] in
theorem measurable_transitionVisitFrom
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (remaining : Nat) :
    Measurable (fun p : State × StepTrace Action State remaining =>
      mdp.transitionVisitFrom targetState targetAction remaining p.1 p.2) := by
  exact measurable_of_finite _

omit [Nonempty State] [Nonempty Action] in
theorem transitionResidualHead_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (targetNextState : State) (currentState : State) (chosenAction : Action)
    (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun nextState =>
        tilt * mdp.transitionResidualHead targetState targetAction targetNextState
            currentState (chosenAction, nextState) -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitHead targetState targetAction
              currentState (chosenAction, nextState))
      1 0 (mdp.transition (currentState, chosenAction)) := by
  by_cases hvisit : currentState = targetState ∧ chosenAction = targetAction
  · let indicator : State -> Real := fun nextState =>
      if nextState = targetNextState then 1 else 0
    let p : Real :=
      (mdp.transition (targetState, targetAction)).real {targetNextState}
    have hindicator_meas : Measurable indicator := measurable_of_finite _
    have hindicator_mem : ∀ nextState, indicator nextState ∈ Set.Icc (0 : Real) 1 := by
      intro nextState
      simp only [indicator]
      split <;> simp
    have hmean :
        ∫ nextState, indicator nextState
            ∂mdp.transition (currentState, chosenAction) = p := by
      have hs : currentState = targetState := hvisit.1
      have ha : chosenAction = targetAction := hvisit.2
      have hindicator_eq : indicator =
          Set.indicator ({targetNextState} : Set State)
            (fun _ : State => (1 : Real)) := by
        funext nextState
        by_cases hnext : nextState = targetNextState
        · simp [indicator, hnext]
        · simp [indicator, hnext]
      rw [hindicator_eq,
        integral_indicator_const (1 : Real)
          (MeasurableSet.singleton targetNextState)]
      simp only [p, hs, ha]
      simp
    have hsub :=
      Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mdp.transition (currentState, chosenAction))
        hindicator_meas.aemeasurable
        (Filter.Eventually.of_forall hindicator_mem) hmean
    have hproxy :
        (((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)) =
          (1 / 4 : Real) := by
      simp [Concentration.intervalVarianceProxy]
      norm_num
    have hfixed : Concentration.HasMGFUpperBoundAt
        (fun nextState => indicator nextState - p)
        tilt (tilt ^ 2 / 8) (mdp.transition (currentState, chosenAction)) := by
      constructor
      · exact hsub.integrable_exp_mul
      ·
        have h := hsub.mgf_le tilt
        rw [hproxy] at h
        convert h using 1 <;> ring
    have hcomp := hfixed.compensated
    convert hcomp using 1
    funext nextState
    rw [show currentState = targetState from hvisit.1,
      show chosenAction = targetAction from hvisit.2]
    simp only [transitionResidualHead, transitionVisitHead, true_and,
      if_true, indicator, p]
    ring
  · have hzero : Concentration.HasMGFUpperBoundAt
        (fun _nextState : State => (0 : Real)) 1 0
        (mdp.transition (currentState, chosenAction)) := by
      constructor
      · intro s
        simpa using (integrable_const (μ := mdp.transition (currentState, chosenAction))
          (Real.exp (s * 0)))
      · simp [ProbabilityTheory.mgf]
    have heq : (fun nextState : State =>
        tilt * mdp.transitionResidualHead targetState targetAction targetNextState
            currentState (chosenAction, nextState) -
          tilt ^ 2 / 8 *
            mdp.transitionVisitHead targetState targetAction
              currentState (chosenAction, nextState)) =
        (fun _nextState : State => (0 : Real)) := by
      funext nextState
      simp only [transitionResidualHead, transitionVisitHead]
      rw [if_neg hvisit, if_neg hvisit]
      ring
    rw [heq]
    exact hzero

omit [Nonempty State] [Nonempty Action] in
/-- One generated action/transition head pays only its realized visit budget. -/
theorem actionStateKernel_transitionResidualHead_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (targetState : State) (targetAction : Action) (targetNextState : State)
    (currentState : State) (stage : Fin mdp.horizon) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun head : Action × State =>
        tilt * mdp.transitionResidualHead targetState targetAction targetNextState
            currentState head -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitHead targetState targetAction currentState head)
      1 0 (policy.actionStateKernel stage currentState) := by
  let Z : Action × State -> Real := fun head =>
    tilt * mdp.transitionResidualHead targetState targetAction targetNextState
        currentState head -
      (tilt ^ 2 / 8) *
        mdp.transitionVisitHead targetState targetAction currentState head
  have hZ : Measurable Z := measurable_of_finite _
  have hint : Integrable (fun head => Real.exp (1 * Z head))
      (policy.actionStateKernel stage currentState) :=
    integrable_of_fintype _ _ (by fun_prop)
  constructor
  · intro s
    exact integrable_of_fintype _ _ (by fun_prop)
  · rw [ProbabilityTheory.mgf]
    change (∫ head, Real.exp (1 * Z head)
      ∂policy.actionStateKernel stage currentState) <= Real.exp 0
    unfold MarkovPolicy.actionStateKernel
    rw [ProbabilityTheory.integral_compProd hint]
    simp only [Real.exp_zero]
    have hinner : ∀ chosenAction : Action,
        (∫ nextState, Real.exp (Z (chosenAction, nextState))
            ∂mdp.transition (currentState, chosenAction)) <= 1 := by
      intro chosenAction
      have h := mdp.transitionResidualHead_compensated_hasMGFUpperBoundAt
        targetState targetAction targetNextState currentState chosenAction tilt
      simpa [ProbabilityTheory.mgf, Z] using h.mgf_le
    have hleft : Integrable
        (fun chosenAction =>
          ∫ nextState, Real.exp (1 * Z (chosenAction, nextState))
            ∂mdp.transition (currentState, chosenAction))
        (policy.actionKernel stage currentState) :=
      integrable_of_fintype _ _ (measurable_of_finite _)
    have hinner' : ∀ chosenAction : Action,
        (∫ nextState, Real.exp (1 * Z (chosenAction, nextState))
            ∂mdp.transition (currentState, chosenAction)) <= 1 := by
      simpa only [one_mul] using hinner
    calc
      (∫ chosenAction,
          ∫ nextState, Real.exp (1 * Z (chosenAction, nextState))
            ∂mdp.transition (currentState, chosenAction)
          ∂policy.actionKernel stage currentState) <=
          ∫ _chosenAction, (1 : Real)
            ∂policy.actionKernel stage currentState := by
              exact integral_mono_ae hleft (integrable_const 1)
                (Filter.Eventually.of_forall hinner')
      _ = 1 := by simp

omit [Nonempty State] [Nonempty Action] in
/--
The whole generated finite trace satisfies the same fixed-tilt exponential
bound, with compensator equal to its literal state-action visit count.
-/
theorem trajectoryKernelRemaining_transitionResidual_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (targetState : State) (targetAction : Action) (targetNextState : State)
    (tilt : Real) (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (currentState : State) :
    Concentration.HasMGFUpperBoundAt
      (fun trace =>
        tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
            remaining currentState trace -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitFrom targetState targetAction
              remaining currentState trace)
      1 0 (policy.trajectoryKernelRemaining remaining hremaining currentState) := by
  induction remaining generalizing currentState with
  | zero =>
      have hzero : Concentration.HasMGFUpperBoundAt
          (fun _trace : StepTrace Action State 0 => (0 : Real)) 1 0
          (policy.trajectoryKernelRemaining 0 hremaining currentState) := by
        constructor
        · intro s
          exact integrable_of_fintype _ _ (by fun_prop)
        · simp [ProbabilityTheory.mgf]
      simpa [transitionResidualFrom, transitionVisitFrom] using hzero
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let tailKernel : ProbabilityTheory.Kernel
          (State × (Action × State)) (StepTrace Action State remaining) :=
        (policy.trajectoryKernelRemaining remaining (by omega)).comap
          (fun p : State × (Action × State) => p.2.2) measurable_snd.snd
      let consStep :=
        fun p : (Action × State) × StepTrace Action State remaining =>
          @Fin.cons remaining (fun _ => Action × State) p.1 p.2
      let Z : StepTrace Action State (remaining + 1) -> Real := fun trace =>
        tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
            (remaining + 1) currentState trace -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitFrom targetState targetAction
              (remaining + 1) currentState trace
      let Zhead : Action × State -> Real := fun head =>
        tilt * mdp.transitionResidualHead targetState targetAction targetNextState
            currentState head -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitHead targetState targetAction currentState head
      let Ztail : (Action × State) × StepTrace Action State remaining -> Real :=
        fun p =>
          tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
              remaining p.1.2 p.2 -
            (tilt ^ 2 / 8) *
              mdp.transitionVisitFrom targetState targetAction remaining p.1.2 p.2
      have hcons : Measurable consStep := StepTrace.measurable_cons remaining
      have hZ : Measurable Z :=
        ((mdp.measurable_transitionResidualFrom targetState targetAction
          targetNextState (remaining + 1)).comp
            (measurable_const.prodMk measurable_id)).const_mul tilt |>.sub
          (((mdp.measurable_transitionVisitFrom targetState targetAction
            (remaining + 1)).comp
              (measurable_const.prodMk measurable_id)).const_mul (tilt ^ 2 / 8))
      have hpair : Integrable (fun p => Real.exp (1 * Z (consStep p)))
          (((policy.actionStateKernel stage).compProd tailKernel) currentState) :=
        integrable_of_fintype _ _ ((Real.measurable_exp.comp
          ((hZ.comp hcons).const_mul 1)))
      have hhead :=
        mdp.actionStateKernel_transitionResidualHead_compensated_hasMGFUpperBoundAt
          policy targetState targetAction targetNextState currentState stage tilt
      have htail : ∀ head : Action × State,
          Concentration.HasMGFUpperBoundAt
            (fun tail => Ztail (head, tail)) 1 0
            (policy.trajectoryKernelRemaining remaining (by omega) head.2) := by
        intro head
        simpa [Ztail] using ih (by omega) head.2
      constructor
      · intro s
        exact integrable_of_fintype _ _ (by fun_prop)
      · rw [ProbabilityTheory.mgf]
        change (∫ trace, Real.exp (1 * Z trace)
          ∂policy.trajectoryKernelRemaining (remaining + 1) hremaining currentState) <=
            Real.exp 0
        rw [MarkovPolicy.trajectoryKernelRemaining]
        rw [ProbabilityTheory.Kernel.map_apply _ hcons]
        change (∫ trace, (fun trace => Real.exp (1 * Z trace)) trace
          ∂Measure.map consStep
            (((policy.actionStateKernel stage).compProd tailKernel)
              currentState)) <= Real.exp 0
        have hfm : AEStronglyMeasurable
            (fun trace => Real.exp (1 * Z trace))
            (Measure.map consStep
              (((policy.actionStateKernel stage).compProd tailKernel)
                currentState)) :=
          (Real.measurable_exp.comp (hZ.const_mul 1)).aestronglyMeasurable
        rw [integral_map hcons.aemeasurable hfm]
        rw [ProbabilityTheory.integral_compProd hpair]
        simp only [Real.exp_zero]
        have hinner : ∀ head : Action × State,
            (∫ tail, Real.exp (1 * Z (consStep (head, tail)))
              ∂tailKernel (currentState, head)) <= Real.exp (Zhead head) := by
          intro head
          have htailApply : tailKernel (currentState, head) =
              policy.trajectoryKernelRemaining remaining (by omega) head.2 := by
            rfl
          rw [htailApply]
          have hz : ∀ tail,
              Z (consStep (head, tail)) = Zhead head + Ztail (head, tail) := by
            intro tail
            simp [Z, Zhead, Ztail, consStep, transitionResidualFrom,
              transitionVisitFrom]
            ring
          simp_rw [hz, mul_add, Real.exp_add, one_mul, integral_const_mul]
          have htailMgf :
              (∫ tail, Real.exp (Ztail (head, tail))
                ∂policy.trajectoryKernelRemaining remaining (by omega) head.2) <= 1 := by
            simpa [ProbabilityTheory.mgf] using (htail head).mgf_le
          simpa using
            (mul_le_mul_of_nonneg_left htailMgf (Real.exp_pos (Zhead head)).le)
        have hleft : Integrable
            (fun head =>
              ∫ tail, Real.exp (1 * Z (consStep (head, tail)))
                ∂tailKernel (currentState, head))
            (policy.actionStateKernel stage currentState) :=
          integrable_of_fintype _ _ (measurable_of_finite _)
        have hright : Integrable (fun head => Real.exp (Zhead head))
            (policy.actionStateKernel stage currentState) :=
          integrable_of_fintype _ _ (measurable_of_finite _)
        calc
          (∫ head,
              ∫ tail, Real.exp (1 * Z (consStep (head, tail)))
                ∂tailKernel (currentState, head)
              ∂policy.actionStateKernel stage currentState) <=
              ∫ head, Real.exp (Zhead head)
                ∂policy.actionStateKernel stage currentState := by
                  exact integral_mono_ae hleft hright
                    (Filter.Eventually.of_forall hinner)
          _ <= 1 := by
            simpa [ProbabilityTheory.mgf, Zhead] using hhead.mgf_le

omit [Nonempty State] [Nonempty Action] in
/-- Residual recursion is exactly the chronological finite sum. -/
theorem transitionResidualFrom_eq_sum
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (targetNextState : State) (remaining : Nat) (currentState : State)
    (trace : StepTrace Action State remaining) :
    mdp.transitionResidualFrom targetState targetAction targetNextState
        remaining currentState trace =
      ∑ stage : Fin remaining,
        mdp.transitionResidualHead targetState targetAction targetNextState
          (StepTrace.stateAt currentState trace stage) (trace stage) := by
  induction remaining generalizing currentState with
  | zero => simp [transitionResidualFrom]
  | succ remaining ih =>
      rw [transitionResidualFrom, Fin.sum_univ_succ]
      congr 1
      rw [ih (trace 0).2 (Fin.tail trace)]
      apply Finset.sum_congr rfl
      intro stage _hstage
      have hstate := StepTrace.stateAt_succ currentState (trace 0)
        (Fin.tail trace) stage
      have htrace : Fin.tail trace stage = trace stage.succ := rfl
      rw [htrace]
      exact congrArg (fun state =>
        mdp.transitionResidualHead targetState targetAction targetNextState
          state (trace stage.succ)) (by simpa using hstate.symm)

omit [Nonempty State] [Nonempty Action] in
/-- Visit recursion is exactly the chronological finite sum. -/
theorem transitionVisitFrom_eq_sum
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (remaining : Nat) (currentState : State)
    (trace : StepTrace Action State remaining) :
    mdp.transitionVisitFrom targetState targetAction remaining currentState trace =
      ∑ stage : Fin remaining,
        mdp.transitionVisitHead targetState targetAction
          (StepTrace.stateAt currentState trace stage) (trace stage) := by
  induction remaining generalizing currentState with
  | zero => simp [transitionVisitFrom]
  | succ remaining ih =>
      rw [transitionVisitFrom, Fin.sum_univ_succ]
      congr 1
      rw [ih (trace 0).2 (Fin.tail trace)]
      apply Finset.sum_congr rfl
      intro stage _hstage
      have hstate := StepTrace.stateAt_succ currentState (trace 0)
        (Fin.tail trace) stage
      have htrace : Fin.tail trace stage = trace stage.succ := rfl
      rw [htrace]
      exact congrArg (fun state =>
        mdp.transitionVisitHead targetState targetAction
          state (trace stage.succ)) (by simpa using hstate.symm)

omit [Nonempty State] [Nonempty Action] in
/--
The full-trace residual is the aggregate transition count minus the true
singleton mass times the aggregate visit count.
-/
theorem transitionResidualFrom_eq_aggregateCounts
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (targetNextState : State)
    (trajectory : State × StepTrace Action State mdp.horizon) :
    mdp.transitionResidualFrom targetState targetAction targetNextState
        mdp.horizon trajectory.1 trajectory.2 =
      ((mdp.episodeBatchOfTrajectories 1 (fun _ => trajectory))
          |>.transitionCountSummary.aggregateTransitionCount
            targetState targetAction targetNextState : Real) -
        ((mdp.episodeBatchOfTrajectories 1 (fun _ => trajectory))
          |>.transitionCountSummary.aggregateVisitCount
            targetState targetAction : Real) *
          (mdp.transition (targetState, targetAction)).real {targetNextState} := by
  rw [mdp.transitionResidualFrom_eq_sum]
  let batch := mdp.episodeBatchOfTrajectories 1 (fun _ => trajectory)
  have htransition :
      (batch.transitionCountSummary.aggregateTransitionCount
          targetState targetAction targetNextState : Real) =
        ∑ stage : Fin mdp.horizon,
          if mdp.trajectoryStateAt trajectory stage = targetState ∧
              (trajectory.2 stage).1 = targetAction ∧
              (trajectory.2 stage).2 = targetNextState then 1 else 0 := by
    unfold TransitionCountSummary.aggregateTransitionCount
    norm_cast
  have hvisitCount :
      (batch.transitionCountSummary.aggregateVisitCount
          targetState targetAction : Real) =
        ∑ stage : Fin mdp.horizon,
          if mdp.trajectoryStateAt trajectory stage = targetState ∧
              (trajectory.2 stage).1 = targetAction then 1 else 0 := by
    unfold TransitionCountSummary.aggregateVisitCount
    norm_cast
    apply Finset.sum_congr rfl
    intro stage _hstage
    rw [EpisodeBatch.transitionCountSummary_visitCount]
    simp [batch, EpisodeBatch.visitCount, MDP.episodeBatchOfTrajectories,
      MDP.episodeStepOfTrajectory]
  change _ =
    (batch.transitionCountSummary.aggregateTransitionCount
      targetState targetAction targetNextState : Real) -
      (batch.transitionCountSummary.aggregateVisitCount
        targetState targetAction : Real) *
        (mdp.transition (targetState, targetAction)).real {targetNextState}
  rw [htransition, hvisitCount, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [mdp.stepTrace_stateAt_eq_trajectoryStateAt]
  apply Finset.sum_congr rfl
  intro stage _hstage
  by_cases hvisit :
      mdp.trajectoryStateAt trajectory stage = targetState ∧
        (trajectory.2 stage).1 = targetAction
  · by_cases hnext : (trajectory.2 stage).2 = targetNextState
    · simp [transitionResidualHead, transitionVisitHead,
        hvisit, hnext]
    · simp [transitionResidualHead, transitionVisitHead,
        hvisit, hnext]
  · simp [transitionResidualHead, transitionVisitHead,
      hvisit]
    aesop

omit [Nonempty State] [Nonempty Action] in
/-- The full-trace compensator is the aggregate visit count of its one-batch image. -/
theorem transitionVisitFrom_eq_aggregateVisitCount
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (trajectory : State × StepTrace Action State mdp.horizon) :
    mdp.transitionVisitFrom targetState targetAction
        mdp.horizon trajectory.1 trajectory.2 =
      ((mdp.episodeBatchOfTrajectories 1 (fun _ => trajectory))
          |>.transitionCountSummary.aggregateVisitCount
            targetState targetAction : Real) := by
  rw [mdp.transitionVisitFrom_eq_sum]
  let batch := mdp.episodeBatchOfTrajectories 1 (fun _ => trajectory)
  change _ =
    (batch.transitionCountSummary.aggregateVisitCount
      targetState targetAction : Real)
  unfold TransitionCountSummary.aggregateVisitCount
  push_cast
  simp_rw [mdp.stepTrace_stateAt_eq_trajectoryStateAt]
  apply Finset.sum_congr rfl
  intro stage _hstage
  rw [EpisodeBatch.transitionCountSummary_visitCount]
  simp [transitionVisitHead, batch, EpisodeBatch.visitCount,
    MDP.episodeBatchOfTrajectories, MDP.episodeStepOfTrajectory]

omit [Nonempty State] [Nonempty Action] in
/-- The compensated fixed-tilt witness after integrating the random initial state. -/
theorem trajectoryMeasure_transitionResidual_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (targetState : State) (targetAction : Action) (targetNextState : State)
    (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory =>
        tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
            mdp.horizon trajectory.1 trajectory.2 -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitFrom targetState targetAction
              mdp.horizon trajectory.1 trajectory.2)
      1 0 (policy.trajectoryMeasure initialState) := by
  let Z : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
        mdp.horizon trajectory.1 trajectory.2 -
      (tilt ^ 2 / 8) *
        mdp.transitionVisitFrom targetState targetAction
          mdp.horizon trajectory.1 trajectory.2
  have hZ : Measurable Z :=
    ((mdp.measurable_transitionResidualFrom targetState targetAction
      targetNextState mdp.horizon).const_mul tilt).sub
      ((mdp.measurable_transitionVisitFrom targetState targetAction
        mdp.horizon).const_mul (tilt ^ 2 / 8))
  constructor
  · intro s
    exact integrable_of_fintype _ _ (Real.measurable_exp.comp (hZ.const_mul s))
  · rw [ProbabilityTheory.mgf]
    change (∫ trajectory, Real.exp (1 * Z trajectory)
      ∂policy.trajectoryMeasure initialState) <= Real.exp 0
    unfold MarkovPolicy.trajectoryMeasure
    have hint : Integrable (fun trajectory => Real.exp (1 * Z trajectory))
        (initialState.compProd
          (policy.trajectoryKernelRemaining mdp.horizon le_rfl)) :=
      integrable_of_fintype _ _ (Real.measurable_exp.comp (hZ.const_mul 1))
    rw [Measure.integral_compProd hint]
    simp only [Real.exp_zero]
    have hfiber : ∀ state : State,
        (∫ trace, Real.exp (1 * Z (state, trace))
          ∂policy.trajectoryKernelRemaining mdp.horizon le_rfl state) <= 1 := by
      intro state
      have h := mdp.trajectoryKernelRemaining_transitionResidual_compensated_hasMGFUpperBoundAt
        policy targetState targetAction targetNextState tilt mdp.horizon le_rfl state
      simpa [ProbabilityTheory.mgf, Z] using h.mgf_le
    have hleft : Integrable
        (fun state => ∫ trace, Real.exp (1 * Z (state, trace))
          ∂policy.trajectoryKernelRemaining mdp.horizon le_rfl state) initialState :=
      integrable_of_fintype _ _ (measurable_of_finite _)
    calc
      (∫ state,
          ∫ trace, Real.exp (1 * Z (state, trace))
            ∂policy.trajectoryKernelRemaining mdp.horizon le_rfl state
          ∂initialState) <= ∫ _state, (1 : Real) ∂initialState := by
            exact integral_mono_ae hleft (integrable_const 1)
              (Filter.Eventually.of_forall hfiber)
      _ = 1 := by simp

end MDP

namespace EpisodeBatch

/-- The generated one-batch aggregate transition residual. -/
noncomputable def aggregateTransitionResidual
    {mdp : MDP State Action} (batch : EpisodeBatch mdp 1)
    (state : State) (action : Action) (nextState : State) : Real :=
  (batch.transitionCountSummary.aggregateTransitionCount state action nextState : Real) -
    (batch.transitionCountSummary.aggregateVisitCount state action : Real) *
      (mdp.transition (state, action)).real {nextState}

/-- The generated one-batch aggregate state-action visit count as a real. -/
def aggregateVisitReal
    {mdp : MDP State Action} (batch : EpisodeBatch mdp 1)
    (state : State) (action : Action) : Real :=
  (batch.transitionCountSummary.aggregateVisitCount state action : Real)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateTransitionResidual
    {mdp : MDP State Action} (state : State) (action : Action)
    (nextState : State) :
    Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.aggregateTransitionResidual state action nextState) := by
  have htable : Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.transitionCountSummary.aggregateTransitionCount) :=
    TransitionCountSummary.measurable_aggregateTransitionCount.comp
      EpisodeBatch.measurable_transitionCountSummary
  have hcount : Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.transitionCountSummary.aggregateTransitionCount
        state action nextState) :=
    (measurable_pi_apply nextState).comp
      ((measurable_pi_apply action).comp
        ((measurable_pi_apply state).comp htable))
  have hvisits : Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.transitionCountSummary.aggregateVisitCount state action) :=
    ((measurable_pi_apply action).comp
      ((measurable_pi_apply state).comp
        TransitionCountSummary.measurable_aggregateVisitCount)).comp
      EpisodeBatch.measurable_transitionCountSummary
  have hcountReal : Measurable (fun batch : EpisodeBatch mdp 1 =>
      (batch.transitionCountSummary.aggregateTransitionCount
        state action nextState : Real)) := by
    simpa [Function.comp_def] using
      ((MeasurableEmbedding.natCast (α := Real)).measurable_comp_iff.mpr hcount)
  have hvisitsReal : Measurable (fun batch : EpisodeBatch mdp 1 =>
      (batch.transitionCountSummary.aggregateVisitCount state action : Real)) := by
    simpa [Function.comp_def] using
      ((MeasurableEmbedding.natCast (α := Real)).measurable_comp_iff.mpr hvisits)
  exact hcountReal.sub
    (hvisitsReal.mul_const ((mdp.transition (state, action)).real {nextState}))

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateVisitReal
    {mdp : MDP State Action} (state : State) (action : Action) :
    Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.aggregateVisitReal state action) := by
  have hvisits : Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.transitionCountSummary.aggregateVisitCount state action) :=
    ((measurable_pi_apply action).comp
      ((measurable_pi_apply state).comp
        TransitionCountSummary.measurable_aggregateVisitCount)).comp
      EpisodeBatch.measurable_transitionCountSummary
  simpa [aggregateVisitReal, Function.comp_def] using
    ((MeasurableEmbedding.natCast (α := Real)).measurable_comp_iff.mpr hvisits)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- One generated episode contributes at most one pooled visit per stage. -/
theorem aggregateVisitCount_le_horizon
    {mdp : MDP State Action} (batch : EpisodeBatch mdp 1)
    (state : State) (action : Action) :
    batch.transitionCountSummary.aggregateVisitCount state action <= mdp.horizon := by
  classical
  unfold TransitionCountSummary.aggregateVisitCount
    TransitionCountSummary.visitCount EpisodeBatch.transitionCountSummary
    EpisodeBatch.transitionCount
  calc
    (∑ stage : Fin mdp.horizon, ∑ nextState : State,
        ∑ episode : Fin 1,
          if (batch episode stage).state = state /\
              (batch episode stage).action = action /\
              (batch episode stage).nextState = nextState then 1 else 0) =
        ∑ stage : Fin mdp.horizon,
          if (batch 0 stage).state = state /\
              (batch 0 stage).action = action then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro stage _
        rw [Finset.sum_comm]
        simp only [Fin.sum_univ_one]
        by_cases hs : (batch 0 stage).state = state
        · by_cases ha : (batch 0 stage).action = action
          · simp [hs, ha]
          · simp [ha]
        · simp [hs]
    _ <= ∑ _stage : Fin mdp.horizon, 1 := by
      exact Finset.sum_le_sum fun stage _ => by split <;> simp
    _ = mdp.horizon := by simp

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The one-episode transition residual is bounded by twice the horizon. -/
theorem abs_aggregateTransitionResidual_le_two_mul_horizon
    {mdp : MDP State Action} (batch : EpisodeBatch mdp 1)
    (state : State) (action : Action) (nextState : State) :
    |batch.aggregateTransitionResidual state action nextState| <=
      2 * (mdp.horizon : Real) := by
  have hprob : (mdp.transition (state, action)).real {nextState} ∈
      Set.Icc (0 : Real) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hrow := batch.transitionCountSummary
    |>.sum_aggregateTransitionCount_eq_aggregateVisitCount state action
  have hcoord :
      batch.transitionCountSummary.aggregateTransitionCount
          state action nextState <=
        batch.transitionCountSummary.aggregateVisitCount state action := by
    rw [← hrow]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ nextState)
  have hvisit := batch.aggregateVisitCount_le_horizon state action
  have hcoordReal :
      (batch.transitionCountSummary.aggregateTransitionCount
        state action nextState : Real) <=
      (batch.transitionCountSummary.aggregateVisitCount state action : Real) := by
    exact_mod_cast hcoord
  have hvisitReal :
      (batch.transitionCountSummary.aggregateVisitCount state action : Real) <=
        (mdp.horizon : Real) := by
    exact_mod_cast hvisit
  have hcoordNonneg : 0 <=
      (batch.transitionCountSummary.aggregateTransitionCount
        state action nextState : Real) := by positivity
  have hvisitNonneg : 0 <=
      (batch.transitionCountSummary.aggregateVisitCount state action : Real) := by
    positivity
  rw [aggregateTransitionResidual, abs_le]
  constructor <;> nlinarith [hprob.1, hprob.2]

end EpisodeBatch

namespace MarkovPolicy

omit [Nonempty State] [Nonempty Action] in
/--
The exact one-episode generated batch law inherits the trace-level compensated
MGF; no independent empirical batch is introduced.
-/
theorem iidEpisodeBatchMeasure_one_aggregateTransitionResidual_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (state : State) (action : Action) (nextState : State) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun batch : EpisodeBatch mdp 1 =>
        tilt * batch.aggregateTransitionResidual state action nextState -
          (tilt ^ 2 / 8) * batch.aggregateVisitReal state action)
      1 0 (policy.iidEpisodeBatchMeasure initialState 1) := by
  let Ztrace : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.transitionResidualFrom state action nextState
        mdp.horizon trajectory.1 trajectory.2 -
      (tilt ^ 2 / 8) *
        mdp.transitionVisitFrom state action mdp.horizon trajectory.1 trajectory.2
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionResidual state action nextState -
      (tilt ^ 2 / 8) * batch.aggregateVisitReal state action
  let eval0 : (Fin 1 -> State × StepTrace Action State mdp.horizon) ->
      State × StepTrace Action State mdp.horizon := Function.eval 0
  let batchMap := mdp.episodeBatchOfTrajectories 1
  have htrace := mdp.trajectoryMeasure_transitionResidual_compensated_hasMGFUpperBoundAt
    policy initialState state action nextState tilt
  have hfamilyMap : Concentration.HasMGFUpperBoundAt Ztrace 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map eval0) := by
    rw [policy.iidTrajectoryFamilyMeasure_map_eval initialState (0 : Fin 1)]
    exact htrace
  have hfamily : Concentration.HasMGFUpperBoundAt (Ztrace ∘ eval0) 1 0
      (policy.iidTrajectoryFamilyMeasure initialState 1) := by
    exact Concentration.HasMGFUpperBoundAt.of_map
      (measurable_pi_apply (0 : Fin 1)).aemeasurable hfamilyMap
  have hpoint : ∀ trajectories : Fin 1 ->
      State × StepTrace Action State mdp.horizon,
      Zbatch (batchMap trajectories) = Ztrace (eval0 trajectories) := by
    intro trajectories
    have hresidual := mdp.transitionResidualFrom_eq_aggregateCounts
      state action nextState (trajectories 0)
    have hvisit := mdp.transitionVisitFrom_eq_aggregateVisitCount
      state action (trajectories 0)
    have hbatchEq : batchMap trajectories =
        mdp.episodeBatchOfTrajectories 1 (fun _ => trajectories 0) := by
      funext episode stage
      have hepisode : episode = (0 : Fin 1) := Subsingleton.elim _ _
      subst episode
      rfl
    change Zbatch (batchMap trajectories) = Ztrace (eval0 trajectories)
    rw [hbatchEq]
    simp only [Zbatch, Ztrace, eval0, Function.eval,
      EpisodeBatch.aggregateTransitionResidual,
      EpisodeBatch.aggregateVisitReal]
    rw [← hresidual, ← hvisit]
  have hcomposed : Concentration.HasMGFUpperBoundAt
      (Zbatch ∘ batchMap) 1 0
      (policy.iidTrajectoryFamilyMeasure initialState 1) := by
    constructor
    · intro s
      have hint := hfamily.integrable_exp_mul s
      apply hint.congr
      exact Filter.Eventually.of_forall fun trajectories => by
        simp only [Function.comp_apply]
        rw [hpoint trajectories]
    · have hmgf := hfamily.mgf_le
      rw [ProbabilityTheory.mgf_congr
        (Filter.Eventually.of_forall fun trajectories => by
          simp only [Function.comp_apply]
          exact hpoint trajectories)]
      exact hmgf
  have hbatchMeas : Measurable batchMap :=
    mdp.measurable_episodeBatchOfTrajectories 1
  have hZbatchMeas : Measurable Zbatch :=
    ((EpisodeBatch.measurable_aggregateTransitionResidual state action nextState).const_mul tilt).sub
      (EpisodeBatch.measurable_aggregateVisitReal state action |>.const_mul (tilt ^ 2 / 8))
  have hid : Concentration.HasMGFUpperBoundAt id 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map (Zbatch ∘ batchMap)) :=
    (Concentration.HasMGFUpperBoundAt.id_map_iff
      (hZbatchMeas.comp hbatchMeas).aemeasurable).2 hcomposed
  unfold iidEpisodeBatchMeasure
  apply (Concentration.HasMGFUpperBoundAt.id_map_iff hZbatchMeas.aemeasurable).1
  rw [Measure.map_map hZbatchMeas hbatchMeas]
  exact hid

end MarkovPolicy

namespace AdaptiveEpisodeBatchSource

/-- Canonical finite-prefix filtration presented with the actual `frestrictLe`
history object consumed by `AdaptiveEpisodeBatchSource`.  It is extensionally
the usual product filtration, but this presentation keeps conditional kernels
definitionally aligned with the generated source. -/
noncomputable def batchPrefixFiltration
    {mdp : MDP State Action} (episodes : Nat) :
    @Filtration (EpisodeBatchTrajectory mdp episodes) Nat _
      MeasurableSpace.pi where
  seq n :=
    @MeasurableSpace.comap
      (EpisodeBatchTrajectory mdp episodes)
      (EpisodeBatchPrefix mdp episodes n)
      (Preorder.frestrictLe n)
      (inferInstance : MeasurableSpace (EpisodeBatchPrefix mdp episodes n))
  mono' i j hij := by
    simpa only [Filtration.piLE_eq_comap_frestrictLe] using
      ((Filtration.piLE
        (X := fun _ : Nat => EpisodeBatch mdp episodes)).mono hij)
  le' n := (Preorder.measurable_frestrictLe
    (X := fun _ : Nat => EpisodeBatch mdp episodes) n).comap_le

/--
Transport pointwise fixed-tilt MGF bounds through an identified conditional
kernel map.  This is the fixed-MGF analogue of the repository's centered
sub-Gaussian condExpKernel bridge.
-/
theorem hasCondMGFUpperBoundAt_of_condExpKernel_map_eq
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hmcond : mcond <= mOmega)
    (X : Omega -> Real) (hX : @Measurable Omega Real mOmega inferInstance X)
    (tilt budget : Real) (target : Omega -> Measure Real)
    (hintegrable : ∀ s, Integrable (fun omega => Real.exp (s * X omega)) mu)
    (hmap : Filter.Eventually
      (fun omega => @Measure.map Omega Real mOmega inferInstance X
          ((@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond) omega) =
        target omega)
      (ae (@MeasureTheory.Measure.trim Omega mcond mOmega mu hmcond)))
    (htarget : Filter.Eventually
      (fun omega => Concentration.HasMGFUpperBoundAt id tilt budget
        (target omega))
      (ae (@MeasureTheory.Measure.trim Omega mcond mOmega mu hmcond))) :
    Concentration.HasCondMGFUpperBoundAt mcond hmcond X tilt budget mu := by
  change Concentration.Kernel.HasMGFUpperBoundAt X tilt budget
    (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond)
    (mu.trim hmcond)
  constructor
  · intro s
    rw [@ProbabilityTheory.condExpKernel_comp_trim
      Omega mcond mOmega _ mu _ hmcond]
    exact hintegrable s
  · filter_upwards [hmap, htarget] with omega hmapOmega htargetOmega
    have hmapBound : Concentration.HasMGFUpperBoundAt id tilt budget
        (@Measure.map Omega Real mOmega inferInstance X
          ((@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond) omega)) := by
      rw [hmapOmega]
      exact htargetOmega
    let condMu :=
      (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond) omega
    exact ((Concentration.HasMGFUpperBoundAt.id_map_iff
      (@Measurable.aemeasurable Omega Real mOmega inferInstance X condMu hX)).1
      hmapBound).mgf_le

/-- Transport a fixed-tilt conditional MGF certificate across propositionally
equal conditioning measurable spaces. -/
theorem hasCondMGFUpperBoundAt_congr_measurableSpace
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond mcond' : MeasurableSpace Omega)
    (hmcond : mcond <= mOmega) (hmcond' : mcond' <= mOmega)
    (hspaces : mcond = mcond')
    (X : Omega -> Real) (tilt budget : Real)
    (h : Concentration.HasCondMGFUpperBoundAt
      mcond hmcond X tilt budget mu) :
    Concentration.HasCondMGFUpperBoundAt
      mcond' hmcond' X tilt budget mu := by
  subst mcond'
  simpa only using h


/-- Residual of the last batch visible in a finite generated prefix. -/
noncomputable def aggregateTransitionResidualPrefix
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (round : Nat) (history : EpisodeBatchPrefix mdp 1 round) : Real :=
  (history ⟨round, Finset.mem_Iic.mpr le_rfl⟩).aggregateTransitionResidual
    state action nextState

/-- Visit count of the last batch visible in a finite generated prefix. -/
def aggregateVisitPrefix
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action)
    (round : Nat) (history : EpisodeBatchPrefix mdp 1 round) : Real :=
  (history ⟨round, Finset.mem_Iic.mpr le_rfl⟩).aggregateVisitReal state action

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateTransitionResidualPrefix
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State) (round : Nat) :
    Measurable (source.aggregateTransitionResidualPrefix
      state action nextState round) := by
  exact (EpisodeBatch.measurable_aggregateTransitionResidual
    state action nextState).comp
      (measurable_pi_apply
        (⟨round, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic round))

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateVisitPrefix
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (round : Nat) :
    Measurable (source.aggregateVisitPrefix state action round) := by
  exact (EpisodeBatch.measurable_aggregateVisitReal state action).comp
    (measurable_pi_apply
      (⟨round, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic round))

/-- The actual one-episode transition residual at adaptive coordinate `round`. -/
noncomputable def aggregateTransitionResidualIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (round : Nat) (trajectory : EpisodeBatchTrajectory mdp 1) : Real :=
  source.aggregateTransitionResidualPrefix state action nextState round
    (Preorder.frestrictLe round trajectory)

/-- The actual pooled visit count at adaptive coordinate `round`. -/
def aggregateVisitIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action)
    (round : Nat) (trajectory : EpisodeBatchTrajectory mdp 1) : Real :=
  source.aggregateVisitPrefix state action round
    (Preorder.frestrictLe round trajectory)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateTransitionResidualIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State) (round : Nat) :
    Measurable (source.aggregateTransitionResidualIncrement
      state action nextState round) :=
  (source.measurable_aggregateTransitionResidualPrefix
    state action nextState round).comp (Preorder.measurable_frestrictLe round)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateVisitIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (round : Nat) :
    Measurable (source.aggregateVisitIncrement state action round) :=
  (source.measurable_aggregateVisitPrefix state action round).comp
    (Preorder.measurable_frestrictLe round)

omit [Nonempty State] [Nonempty Action] in
/-- The compensated residual process is adapted to the canonical prefix filtration. -/
theorem aggregateTransitionResidual_compensated_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (tilt varianceCoeff : Real) :
    StronglyAdapted
      (batchPrefixFiltration (mdp := mdp) 1)
      (fun round trajectory =>
        tilt * source.aggregateTransitionResidualIncrement
            state action nextState round trajectory -
          varianceCoeff * source.aggregateVisitIncrement
            state action round trajectory) := by
  intro round
  have hprefix : Measurable (fun history : EpisodeBatchPrefix mdp 1 round =>
      tilt * source.aggregateTransitionResidualPrefix
          state action nextState round history -
        varianceCoeff * source.aggregateVisitPrefix
          state action round history) :=
    (source.measurable_aggregateTransitionResidualPrefix
        state action nextState round
      |>.const_mul tilt).sub
      (source.measurable_aggregateVisitPrefix state action round
        |>.const_mul varianceCoeff)
  exact (hprefix.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

omit [DecidableEq State] [DecidableEq Action] in
/--
Any measurable real statistic of the next generated episode has exactly the
mapped history kernel as its regular conditional law.  This reusable bridge is
stated for the whole generated batch, so downstream confidence proofs do not
replace the recurrent process by an offline batch model.
-/
theorem trajectoryMeasure_condDistrib_batchStatistic
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (statistic : EpisodeBatch mdp episodes -> Real)
    (hstatistic : Measurable statistic) :
    ProbabilityTheory.condDistrib
        (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
          statistic (trajectory (n + 1)))
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      (source.batchKernel n).map statistic := by
  letI : ProbabilityTheory.IsMarkovKernel (source.batchKernel n) :=
    source.batchKernel_isMarkov n
  have hcomp :
      ProbabilityTheory.condDistrib
          (statistic ∘
            (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
              trajectory (n + 1)))
          (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
            source.trajectoryMeasure.map (Preorder.frestrictLe n)]
        (ProbabilityTheory.condDistrib
          (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
            trajectory (n + 1))
          (Preorder.frestrictLe n) source.trajectoryMeasure).map statistic :=
    ProbabilityTheory.condDistrib_comp
      (μ := source.trajectoryMeasure)
      (Preorder.frestrictLe n)
      (measurable_pi_apply (n + 1)).aemeasurable
      hstatistic
  filter_upwards [hcomp, source.trajectoryMeasure_condDistrib n] with history hc hk
  have hmap :
      ((ProbabilityTheory.condDistrib
          (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
            trajectory (n + 1))
          (Preorder.frestrictLe n) source.trajectoryMeasure).map statistic) history =
        ((source.batchKernel n).map statistic) history := by
    rw [ProbabilityTheory.Kernel.map_apply _ hstatistic,
      ProbabilityTheory.Kernel.map_apply _ hstatistic, hk]
  simpa only [Function.comp_def] using hc.trans hmap

omit [DecidableEq State] [DecidableEq Action] in
/--
Trimmed conditional-expectation-kernel law for an arbitrary measurable real
statistic of the next generated episode.
-/
theorem condExpKernel_map_batchStatistic_eq_batchKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (statistic : EpisodeBatch mdp episodes -> Real)
    (hstatistic : Measurable statistic) :
    Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        Measure.map
            (fun path : EpisodeBatchTrajectory mdp episodes =>
              statistic (path (n + 1)))
            (ProbabilityTheory.condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (EpisodeBatchPrefix mdp episodes n)).comap
                  (Preorder.frestrictLe n)) trajectory) =
          ((source.batchKernel n).map statistic)
            (Preorder.frestrictLe n trajectory))
      (ae (source.trajectoryMeasure.trim
        (Preorder.measurable_frestrictLe n).comap_le)) := by
  letI : ProbabilityTheory.IsMarkovKernel (source.batchKernel n) :=
    source.batchKernel_isMarkov n
  letI : ProbabilityTheory.IsMarkovKernel
      ((source.batchKernel n).map statistic) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map
      (source.batchKernel n) hstatistic
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      source.trajectoryMeasure
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        statistic (trajectory (n + 1)))
      (Preorder.frestrictLe n)
      (hstatistic.comp (measurable_pi_apply (n + 1)))
      (Preorder.measurable_frestrictLe n)
      ((source.batchKernel n).map statistic)
      (source.trajectoryMeasure_condDistrib_batchStatistic n statistic hstatistic)

omit [Nonempty State] [Nonempty Action] in
/-- Every compensated adaptive residual increment is globally exponentially integrable. -/
theorem integrable_exp_mul_aggregateTransitionResidual_compensatedIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (round : Nat) (tilt varianceCoeff s : Real) :
    Integrable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      Real.exp (s *
        (tilt * source.aggregateTransitionResidualIncrement
            state action nextState round trajectory -
          varianceCoeff * source.aggregateVisitIncrement
            state action round trajectory))) source.trajectoryMeasure := by
  let X := fun trajectory : EpisodeBatchTrajectory mdp 1 =>
    tilt * source.aggregateTransitionResidualIncrement
        state action nextState round trajectory -
      varianceCoeff * source.aggregateVisitIncrement
        state action round trajectory
  have hX : Measurable X :=
    (source.measurable_aggregateTransitionResidualIncrement
      state action nextState round |>.const_mul tilt).sub
      (source.measurable_aggregateVisitIncrement state action round
        |>.const_mul varianceCoeff)
  let bound := |tilt| * (2 * (mdp.horizon : Real)) +
    |varianceCoeff| * (mdp.horizon : Real)
  have hbound : ∀ trajectory : EpisodeBatchTrajectory mdp 1,
      |X trajectory| <= bound := by
    intro trajectory
    have hres := (trajectory round)
      |>.abs_aggregateTransitionResidual_le_two_mul_horizon
        state action nextState
    have hvisNat := (trajectory round).aggregateVisitCount_le_horizon state action
    have hvis : (trajectory round).aggregateVisitReal state action <=
        (mdp.horizon : Real) := by
      unfold EpisodeBatch.aggregateVisitReal
      exact_mod_cast hvisNat
    have hvisNonneg : 0 <= (trajectory round).aggregateVisitReal state action := by
      unfold EpisodeBatch.aggregateVisitReal
      positivity
    calc
      |X trajectory| <=
          |tilt * source.aggregateTransitionResidualIncrement
              state action nextState round trajectory| +
            |varianceCoeff * source.aggregateVisitIncrement
              state action round trajectory| := abs_sub _ _
      _ = |tilt| *
            |source.aggregateTransitionResidualIncrement
              state action nextState round trajectory| +
          |varianceCoeff| *
            |source.aggregateVisitIncrement state action round trajectory| := by
          rw [abs_mul, abs_mul]
      _ <= bound := by
        have hres' : |source.aggregateTransitionResidualIncrement
              state action nextState round trajectory| <=
            2 * (mdp.horizon : Real) := by
          simpa [aggregateTransitionResidualIncrement,
            aggregateTransitionResidualPrefix,
            Preorder.frestrictLe_apply] using hres
        have hvis' : |source.aggregateVisitIncrement
              state action round trajectory| <= (mdp.horizon : Real) := by
          rw [abs_of_nonneg]
          · simpa [aggregateVisitIncrement, aggregateVisitPrefix,
              Preorder.frestrictLe_apply] using hvis
          · simpa [aggregateVisitIncrement, aggregateVisitPrefix,
              Preorder.frestrictLe_apply] using hvisNonneg
        exact add_le_add
          (mul_le_mul_of_nonneg_left hres' (abs_nonneg tilt))
          (mul_le_mul_of_nonneg_left hvis' (abs_nonneg varianceCoeff))
  apply Integrable.of_bound
    ((Real.continuous_exp.measurable.comp (measurable_const.mul hX)).aestronglyMeasurable)
    (Real.exp (|s| * bound))
  exact Filter.Eventually.of_forall fun trajectory => by
    change |Real.exp (s * X trajectory)| <= Real.exp (|s| * bound)
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      s * X trajectory <= |s| * |X trajectory| :=
        (le_abs_self (s * X trajectory)).trans_eq (abs_mul _ _)
      _ <= |s| * bound :=
        mul_le_mul_of_nonneg_left (hbound trajectory) (abs_nonneg s)

/--
At every successor episode, the actual transition residual has the same
visit-charged fixed-tilt conditional MGF under the recurrent source law.
-/
theorem aggregateTransitionResidual_succ_compensated_hasCondMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (n : Nat) (tilt : Real) :
    Concentration.HasCondMGFUpperBoundAt (mΩ := MeasurableSpace.pi)
      (batchPrefixFiltration (mdp := mdp) 1 n)
      ((batchPrefixFiltration (mdp := mdp) 1).le n)
      (fun trajectory =>
        tilt * source.aggregateTransitionResidualIncrement
            state action nextState (n + 1) trajectory -
          (tilt ^ 2 / 8) * source.aggregateVisitIncrement
            state action (n + 1) trajectory)
      1 0 source.trajectoryMeasure := by
  let prefixMap : EpisodeBatchTrajectory mdp 1 -> EpisodeBatchPrefix mdp 1 n :=
    Preorder.frestrictLe n
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionResidual state action nextState -
      (tilt ^ 2 / 8) * batch.aggregateVisitReal state action
  have hZbatch : Measurable Zbatch :=
    (EpisodeBatch.measurable_aggregateTransitionResidual state action nextState
      |>.const_mul tilt).sub
      (EpisodeBatch.measurable_aggregateVisitReal state action
        |>.const_mul (tilt ^ 2 / 8))
  have hX : Measurable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      Zbatch (trajectory (n + 1))) :=
    hZbatch.comp (measurable_pi_apply (n + 1))
  have hkernel :=
    source.condExpKernel_map_batchStatistic_eq_batchKernel n Zbatch hZbatch
  let target : EpisodeBatchTrajectory mdp 1 -> Measure Real := fun trajectory =>
    ((source.batchKernel n).map Zbatch) (prefixMap trajectory)
  have htarget : Filter.Eventually
      (fun trajectory => Concentration.HasMGFUpperBoundAt id 1 0
        (target trajectory))
      (ae (source.trajectoryMeasure.trim
        ((batchPrefixFiltration (mdp := mdp) 1).le n))) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbatch :=
        policy.iidEpisodeBatchMeasure_one_aggregateTransitionResidual_compensated_hasMGFUpperBoundAt
          initialState state action nextState tilt
      have hbatch' : Concentration.HasMGFUpperBoundAt Zbatch 1 0
          (source.batchKernel n history) := by
        rw [source.batchKernel_eq_iidEpisodeBatchMeasure n history]
        simpa [Zbatch] using hbatch
      change Concentration.HasMGFUpperBoundAt id 1 0
        (((source.batchKernel n).map Zbatch) history)
      rw [ProbabilityTheory.Kernel.map_apply _ hZbatch]
      exact (Concentration.HasMGFUpperBoundAt.id_map_iff
        hZbatch.aemeasurable).2 hbatch'
  have hintegrable : ∀ s, Integrable
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        Real.exp (s * Zbatch (trajectory (n + 1))))
      source.trajectoryMeasure := by
    intro s
    simpa [Zbatch, aggregateTransitionResidualIncrement,
      aggregateTransitionResidualPrefix, aggregateVisitIncrement,
      aggregateVisitPrefix, Preorder.frestrictLe_apply] using
      source.integrable_exp_mul_aggregateTransitionResidual_compensatedIncrement
        state action nextState (n + 1) tilt (tilt ^ 2 / 8) s
  have hcomap : Concentration.HasCondMGFUpperBoundAt
      (mΩ := MeasurableSpace.pi)
      (batchPrefixFiltration (mdp := mdp) 1 n)
      ((batchPrefixFiltration (mdp := mdp) 1).le n)
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        Zbatch (trajectory (n + 1))) 1 0 source.trajectoryMeasure :=
    hasCondMGFUpperBoundAt_of_condExpKernel_map_eq
      source.trajectoryMeasure (batchPrefixFiltration (mdp := mdp) 1 n)
      ((batchPrefixFiltration (mdp := mdp) 1).le n)
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        Zbatch (trajectory (n + 1))) hX 1 0 target hintegrable
      (by simpa [target, prefixMap, batchPrefixFiltration] using hkernel)
      htarget
  simpa [Zbatch, aggregateTransitionResidualIncrement,
    aggregateTransitionResidualPrefix, aggregateVisitIncrement,
    aggregateVisitPrefix, Preorder.frestrictLe_apply] using hcomap

/-- Coordinate zero has the same compensated MGF certificate under the exact
initial marginal of the generated recurrent trajectory. -/
theorem aggregateTransitionResidual_zero_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        tilt * source.aggregateTransitionResidualIncrement
            state action nextState 0 trajectory -
          (tilt ^ 2 / 8) * source.aggregateVisitIncrement
            state action 0 trajectory)
      1 0 source.trajectoryMeasure := by
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionResidual state action nextState -
      (tilt ^ 2 / 8) * batch.aggregateVisitReal state action
  have hbatch : Concentration.HasMGFUpperBoundAt Zbatch 1 0
      (source.initialPolicy.iidEpisodeBatchMeasure initialState 1) := by
    simpa [Zbatch] using
      source.initialPolicy.iidEpisodeBatchMeasure_one_aggregateTransitionResidual_compensated_hasMGFUpperBoundAt
        initialState state action nextState tilt
  rw [← source.trajectoryMeasure_map_eval_zero] at hbatch
  have hlift := Concentration.HasMGFUpperBoundAt.of_map
    (X := Zbatch)
    (Z := fun trajectory : EpisodeBatchTrajectory mdp 1 => trajectory 0)
    (measurable_pi_apply 0).aemeasurable hbatch
  simpa [Zbatch, aggregateTransitionResidualIncrement,
    aggregateTransitionResidualPrefix, aggregateVisitIncrement,
    aggregateVisitPrefix, Preorder.frestrictLe_apply] using hlift

omit [Nonempty State] [Nonempty Action] in
/-- Summing the adaptive one-batch residuals through coordinate `round`
recovers the exact pooled numerator minus its true transition mass. -/
theorem sum_aggregateTransitionResidualIncrement_eq_prefixAggregateResidual
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (trajectory : EpisodeBatchTrajectory mdp 1) (round : Nat)
    (state : State) (action : Action) (nextState : State) :
    (∑ i ∈ Finset.range (round + 1),
        source.aggregateTransitionResidualIncrement
          state action nextState i trajectory) =
      (adaptiveCumulativeAggregateTransitionCountAt trajectory round
          state action nextState : Real) -
        (adaptiveCumulativeAggregateVisitCountAt trajectory round
          state action : Real) *
          (mdp.transition (state, action)).real {nextState} := by
  classical
  simp only [aggregateTransitionResidualIncrement,
    aggregateTransitionResidualPrefix, Preorder.frestrictLe_apply,
    EpisodeBatch.aggregateTransitionResidual]
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul]
  have htransition :
      (∑ i ∈ Finset.range (round + 1),
          ((trajectory i).transitionCountSummary.aggregateTransitionCount
            state action nextState : Real)) =
        (adaptiveCumulativeAggregateTransitionCountAt trajectory round
          state action nextState : Real) := by
    rw [adaptiveCumulativeAggregateTransitionCountAt_eq_sum]
    rw [← Fin.sum_univ_eq_sum_range]
    norm_cast
  have hvisit :
      (∑ i ∈ Finset.range (round + 1),
          ((trajectory i).transitionCountSummary.aggregateVisitCount
            state action : Real)) =
        (adaptiveCumulativeAggregateVisitCountAt trajectory round
          state action : Real) := by
    rw [adaptiveCumulativeAggregateVisitCountAt_eq_sum]
    rw [← Fin.sum_univ_eq_sum_range]
    norm_cast
    apply Finset.sum_congr rfl
    intro i _hi
    unfold TransitionCountSummary.aggregateVisitCount
    simp only [EpisodeBatch.transitionCountSummary_visitCount]
  rw [htransition, hvisit]

omit [Nonempty State] [Nonempty Action] in
/-- The compensator sum is literally the aggregate visit denominator used by
the recurrent planner at the same generated prefix. -/
theorem sum_aggregateVisitIncrement_eq_prefixAggregateVisitCount
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (trajectory : EpisodeBatchTrajectory mdp 1) (round : Nat)
    (state : State) (action : Action) :
    (∑ i ∈ Finset.range (round + 1),
        source.aggregateVisitIncrement state action i trajectory) =
      (adaptiveCumulativeAggregateVisitCountAt trajectory round
        state action : Real) := by
  classical
  simp only [aggregateVisitIncrement, aggregateVisitPrefix,
    Preorder.frestrictLe_apply, EpisodeBatch.aggregateVisitReal]
  rw [adaptiveCumulativeAggregateVisitCountAt_eq_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  norm_cast
  apply Finset.sum_congr rfl
  intro i _hi
  unfold TransitionCountSummary.aggregateVisitCount
  simp only [EpisodeBatch.transitionCountSummary_visitCount]

/-- Fixed-tilt, actual-count upper tail for one pooled transition coordinate
on a finite prefix of the generated recurrent process.  The random count is
retained in the event; no expected-occupancy lower bound is substituted. -/
theorem measure_aggregateTransitionResidualSum_ge_inter_visitSum_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (rounds : Nat) (tilt threshold visitBudget : Real)
    (htilt : 0 < tilt) :
    source.trajectoryMeasure
        {trajectory |
          threshold <=
              ∑ i ∈ Finset.range rounds,
                source.aggregateTransitionResidualIncrement
                  state action nextState i trajectory ∧
            (∑ i ∈ Finset.range rounds,
                source.aggregateVisitIncrement state action i trajectory) <=
              visitBudget} <=
      ENNReal.ofReal
        (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) := by
  let F := batchPrefixFiltration (mdp := mdp) 1
  let Y : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    source.aggregateTransitionResidualIncrement
      state action nextState i trajectory
  let V : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    source.aggregateVisitIncrement state action i trajectory
  let Z : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    tilt * Y i trajectory - (tilt ^ 2 / 8) * V i trajectory
  have hadapted : StronglyAdapted F Z := by
    simpa [F, Y, V, Z] using
      source.aggregateTransitionResidual_compensated_stronglyAdapted_piLE
        state action nextState tilt (tilt ^ 2 / 8)
  have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 0
      source.trajectoryMeasure := by
    simpa [Y, V, Z] using
      source.aggregateTransitionResidual_zero_compensated_hasMGFUpperBoundAt
        state action nextState tilt
  have hsucc : ∀ i, i < rounds - 1 ->
      Concentration.HasCondMGFUpperBoundAt
        (F i) (F.le i) (Z (i + 1)) 1 0 source.trajectoryMeasure := by
    intro i _hi
    simpa [F, Y, V, Z] using
      source.aggregateTransitionResidual_succ_compensated_hasCondMGFUpperBoundAt
        state action nextState i tilt
  simpa [Y, V] using
    (Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
      (μ := source.trajectoryMeasure) (ℱ := F) Y V rounds tilt
      (tilt ^ 2 / 8) threshold visitBudget hadapted hzero hsucc htilt.le
      (by positivity))

/-- Two-sided version of the exact-count prefix tail.  Both signs are proved
from the same generated conditional law; the factor two is only the final
finite union. -/
theorem measure_abs_aggregateTransitionResidualSum_ge_inter_visitSum_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (rounds : Nat) (tilt threshold visitBudget : Real)
    (htilt : 0 < tilt) :
    source.trajectoryMeasure
        {trajectory |
          threshold <=
              |∑ i ∈ Finset.range rounds,
                source.aggregateTransitionResidualIncrement
                  state action nextState i trajectory| ∧
            (∑ i ∈ Finset.range rounds,
                source.aggregateVisitIncrement state action i trajectory) <=
              visitBudget} <=
      2 * ENNReal.ofReal
        (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) := by
  let positive : Set (EpisodeBatchTrajectory mdp 1) :=
    {trajectory |
      threshold <= ∑ i ∈ Finset.range rounds,
        source.aggregateTransitionResidualIncrement
          state action nextState i trajectory ∧
      (∑ i ∈ Finset.range rounds,
        source.aggregateVisitIncrement state action i trajectory) <= visitBudget}
  let negative : Set (EpisodeBatchTrajectory mdp 1) :=
    {trajectory |
      threshold <= ∑ i ∈ Finset.range rounds,
        -source.aggregateTransitionResidualIncrement
          state action nextState i trajectory ∧
      (∑ i ∈ Finset.range rounds,
        source.aggregateVisitIncrement state action i trajectory) <= visitBudget}
  have hpos := source.measure_aggregateTransitionResidualSum_ge_inter_visitSum_le
    state action nextState rounds tilt threshold visitBudget htilt
  have hneg : source.trajectoryMeasure negative <=
      ENNReal.ofReal
        (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) := by
    -- Re-apply the compensated theorem to `-Y` with positive tilt.  The
    -- generated MGF producer accepts every real tilt, so this is exactly the
    -- certificate at `-tilt` after elementary normalization.
    let F := batchPrefixFiltration (mdp := mdp) 1
    let Y : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      -source.aggregateTransitionResidualIncrement
        state action nextState i trajectory
    let V : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      source.aggregateVisitIncrement state action i trajectory
    let Z : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      tilt * Y i trajectory - (tilt ^ 2 / 8) * V i trajectory
    have hadapted : StronglyAdapted F Z := by
      have h :=
        source.aggregateTransitionResidual_compensated_stronglyAdapted_piLE
          state action nextState (-tilt) ((-tilt) ^ 2 / 8)
      simpa [F, Y, V, Z] using h
    have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 0
        source.trajectoryMeasure := by
      have h :=
        source.aggregateTransitionResidual_zero_compensated_hasMGFUpperBoundAt
          state action nextState (-tilt)
      simpa [Y, V, Z] using h
    have hsucc : ∀ i, i < rounds - 1 ->
        Concentration.HasCondMGFUpperBoundAt
          (F i) (F.le i) (Z (i + 1)) 1 0 source.trajectoryMeasure := by
      intro i _hi
      have h :=
        source.aggregateTransitionResidual_succ_compensated_hasCondMGFUpperBoundAt
          state action nextState i (-tilt)
      simpa [F, Y, V, Z] using h
    simpa [negative, Y, V] using
      (Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
        (μ := source.trajectoryMeasure) (ℱ := F) Y V rounds tilt
        (tilt ^ 2 / 8) threshold visitBudget hadapted hzero hsucc htilt.le
        (by positivity))
  have hsubset :
      {trajectory |
          threshold <=
              |∑ i ∈ Finset.range rounds,
                source.aggregateTransitionResidualIncrement
                  state action nextState i trajectory| ∧
            (∑ i ∈ Finset.range rounds,
                source.aggregateVisitIncrement state action i trajectory) <=
              visitBudget} ⊆ positive ∪ negative := by
    intro trajectory htrajectory
    rcases htrajectory with ⟨habs, hvis⟩
    rw [le_abs] at habs
    rcases habs with hpos' | hneg'
    · left
      exact ⟨hpos', hvis⟩
    · right
      refine ⟨?_, hvis⟩
      simpa [negative, Finset.sum_neg_distrib] using hneg'
  calc
    source.trajectoryMeasure _ <= source.trajectoryMeasure (positive ∪ negative) :=
      measure_mono hsubset
    _ <= source.trajectoryMeasure positive + source.trajectoryMeasure negative :=
      measure_union_le _ _
    _ <= ENNReal.ofReal
          (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) +
        ENNReal.ofReal
          (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) :=
      add_le_add (by simpa [positive] using hpos) hneg
    _ = 2 * ENNReal.ofReal
          (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) := by
      ring

end AdaptiveEpisodeBatchSource

end BanditRLProof.FiniteHorizonRL
