import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVISameSourceConfidence
import BanditRLProof.Exp3ComparatorBernstein

/-!
# Variance-sensitive same-source transition coordinates for UCBVI-CH

The Hoeffding producer records the exact generated visit compensator.  The
UCBVI-CH analysis additionally needs the Bernoulli variance of each next-state
coordinate.  This module proves that stronger fixed-tilt leaf from the same
transition kernel.  It is not an independent sample model.
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
    [Nonempty State] [Nonempty Action]

namespace MDP

/-- True Bernoulli variance of one transition singleton. -/
noncomputable def transitionCoordinateVariance
    (mdp : MDP State Action) (state : State) (action : Action)
    (nextState : State) : Real :=
  let p := (mdp.transition (state, action)).real {nextState}
  p * (1 - p)

omit [Nonempty State] [Nonempty Action] in
theorem transitionCoordinateVariance_nonneg
    (mdp : MDP State Action) (state : State) (action : Action)
    (nextState : State) :
    0 <= mdp.transitionCoordinateVariance state action nextState := by
  unfold transitionCoordinateVariance
  exact mul_nonneg measureReal_nonneg (sub_nonneg.mpr measureReal_le_one)

omit [Nonempty State] [Nonempty Action] in
/-- A centered transition indicator has exact second moment `p(1-p)`. -/
theorem integral_sq_indicator_sub_transitionMass
    (mdp : MDP State Action) (state : State) (action : Action)
    (nextState : State) :
    (∫ y, ((if y = nextState then 1 else 0) -
          (mdp.transition (state, action)).real {nextState}) ^ 2
        ∂mdp.transition (state, action)) =
      mdp.transitionCoordinateVariance state action nextState := by
  let p : Real := (mdp.transition (state, action)).real {nextState}
  let indicator : State -> Real := fun y => if y = nextState then 1 else 0
  have hindicator : Measurable indicator := measurable_of_finite _
  have hindicator_eq : indicator =
      Set.indicator ({nextState} : Set State) (fun _ : State => (1 : Real)) := by
    funext y
    by_cases hy : y = nextState <;> simp [indicator, hy]
  have hmean : (∫ y, indicator y ∂mdp.transition (state, action)) = p := by
    rw [hindicator_eq,
      integral_indicator_const (1 : Real) (MeasurableSet.singleton nextState)]
    simp [p]
  have hsq : (∫ y, (indicator y) ^ 2 ∂mdp.transition (state, action)) = p := by
    have hpoint : (fun y => (indicator y) ^ 2) = indicator := by
      funext y
      simp [indicator]
    rw [hpoint, hmean]
  have hi : Integrable indicator (mdp.transition (state, action)) :=
    integrable_of_fintype _ _ hindicator
  have hi2 : Integrable (fun y => (indicator y) ^ 2)
      (mdp.transition (state, action)) :=
    integrable_of_fintype _ _ (hindicator.pow_const 2)
  have himem : MemLp indicator 2 (mdp.transition (state, action)) :=
    memLp_of_bounded
      (Filter.Eventually.of_forall (fun y => by
        show indicator y ∈ Set.Icc (0 : Real) 1
        simp only [indicator]
        split <;> norm_num))
      hindicator.aestronglyMeasurable 2
  change (∫ y, (indicator y - p) ^ 2
      ∂mdp.transition (state, action)) = _
  calc
    (∫ y, (indicator y - p) ^ 2 ∂mdp.transition (state, action)) =
        ProbabilityTheory.variance indicator (mdp.transition (state, action)) := by
      rw [ProbabilityTheory.variance_eq_integral hindicator.aemeasurable, hmean]
    _ = p - p ^ 2 := by
      rw [ProbabilityTheory.variance_eq_sub himem]
      change (∫ y, indicator y ^ 2 ∂mdp.transition (state, action)) -
          (∫ y, indicator y ∂mdp.transition (state, action)) ^ 2 = _
      rw [hsq, hmean]
    _ = mdp.transitionCoordinateVariance state action nextState := by
      simp [transitionCoordinateVariance, p]
      ring

omit [Nonempty State] [Nonempty Action] in
/-- The visited transition singleton has a variance-sensitive compensated MGF.
The hard `|tilt| <= 1` contract is the standard Bernstein small-tilt range. -/
theorem transitionResidualHead_variance_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (targetState : State) (targetAction : Action)
    (targetNextState : State) (currentState : State) (chosenAction : Action)
    (tilt : Real) (htilt : |tilt| <= 1) :
    Concentration.HasMGFUpperBoundAt
      (fun nextState =>
        tilt * mdp.transitionResidualHead targetState targetAction targetNextState
            currentState (chosenAction, nextState) -
          tilt ^ 2 *
            mdp.transitionCoordinateVariance
              targetState targetAction targetNextState *
            mdp.transitionVisitHead targetState targetAction
              currentState (chosenAction, nextState))
      1 0 (mdp.transition (currentState, chosenAction)) := by
  by_cases hvisit : currentState = targetState ∧ chosenAction = targetAction
  · rcases hvisit with ⟨hstate, haction⟩
    subst currentState
    subst chosenAction
    let p : Real :=
      (mdp.transition (targetState, targetAction)).real {targetNextState}
    let X : State -> Real := fun y =>
      (if y = targetNextState then 1 else 0) - p
    have hX : Measurable X := measurable_of_finite _
    have hXabs : ∀ y, |tilt * X y| <= 1 := by
      intro y
      have hp : p ∈ Set.Icc (0 : Real) 1 :=
        ⟨measureReal_nonneg, measureReal_le_one⟩
      rcases hp with ⟨hp0, hp1⟩
      have hxy : |X y| <= 1 := by
        simp only [X]
        split <;> rw [abs_le] <;> constructor <;> linarith
      calc
        |tilt * X y| = |tilt| * |X y| := abs_mul _ _
        _ <= 1 * 1 := mul_le_mul htilt hxy (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hmean : (∫ y, X y ∂mdp.transition (targetState, targetAction)) = 0 := by
      let indicator : State -> Real := fun y => if y = targetNextState then 1 else 0
      have hindicator_eq : indicator =
          Set.indicator ({targetNextState} : Set State) (fun _ : State => (1 : Real)) := by
        funext y
        by_cases hy : y = targetNextState <;> simp [indicator, hy]
      have hi : Integrable indicator (mdp.transition (targetState, targetAction)) :=
        integrable_of_fintype _ _ (measurable_of_finite _)
      change (∫ y, indicator y - p ∂mdp.transition (targetState, targetAction)) = 0
      rw [integral_sub hi (integrable_const _)]
      rw [hindicator_eq,
        integral_indicator_const (1 : Real) (MeasurableSet.singleton targetNextState)]
      simp [p]
    have hsecond : (∫ y, (X y) ^ 2
        ∂mdp.transition (targetState, targetAction)) =
        mdp.transitionCoordinateVariance
          targetState targetAction targetNextState := by
      simpa [X, p] using
        mdp.integral_sq_indicator_sub_transitionMass
          targetState targetAction targetNextState
    have hbase : Concentration.HasMGFUpperBoundAt X tilt
        (tilt ^ 2 * mdp.transitionCoordinateVariance
          targetState targetAction targetNextState)
        (mdp.transition (targetState, targetAction)) := by
      constructor
      · intro s
        exact integrable_of_fintype _ _ (by fun_prop)
      · rw [ProbabilityTheory.mgf]
        have hexp : ∀ y, Real.exp (tilt * X y) <=
            1 + tilt * X y + (tilt * X y) ^ 2 := fun y =>
          Concentration.exp_le_one_add_self_add_sq_of_abs_le_one (hXabs y)
        have hleft : Integrable (fun y => Real.exp (tilt * X y))
            (mdp.transition (targetState, targetAction)) :=
          integrable_of_fintype _ _ (by fun_prop)
        have hright : Integrable
            (fun y => 1 + tilt * X y + (tilt * X y) ^ 2)
            (mdp.transition (targetState, targetAction)) :=
          integrable_of_fintype _ _ (by fun_prop)
        calc
          (∫ y, Real.exp (tilt * X y)
              ∂mdp.transition (targetState, targetAction)) <=
              ∫ y, (1 + tilt * X y + (tilt * X y) ^ 2)
                ∂mdp.transition (targetState, targetAction) :=
            integral_mono_ae hleft hright (Filter.Eventually.of_forall hexp)
          _ = 1 + tilt ^ 2 * mdp.transitionCoordinateVariance
                targetState targetAction targetNextState := by
            rw [integral_add, integral_add]
            · simp_rw [mul_pow]
              rw [integral_const, integral_const_mul, hmean,
                integral_const_mul, hsecond]
              simp
            all_goals exact integrable_of_fintype _ _ (by fun_prop)
          _ <= Real.exp (tilt ^ 2 * mdp.transitionCoordinateVariance
                targetState targetAction targetNextState) := by
            simpa [add_comm] using Real.add_one_le_exp
              (tilt ^ 2 * mdp.transitionCoordinateVariance
                targetState targetAction targetNextState)
    have hcomp := hbase.compensated
    convert hcomp using 1
    funext y
    simp [transitionResidualHead, transitionVisitHead, X, p]
  · have hzero : Concentration.HasMGFUpperBoundAt
        (fun _ : State => (0 : Real)) 1 0
        (mdp.transition (currentState, chosenAction)) := by
      constructor
      · intro s
        simpa using (integrable_const
          (mu := mdp.transition (currentState, chosenAction)) (Real.exp (s * 0)))
      · simp [ProbabilityTheory.mgf]
    convert hzero using 1
    funext y
    simp [transitionResidualHead, transitionVisitHead, hvisit]

omit [Nonempty State] [Nonempty Action] in
/-- The generated action/transition head preserves the exact coordinate
variance compensator. -/
theorem actionStateKernel_transitionResidualHead_variance_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (targetState : State) (targetAction : Action) (targetNextState : State)
    (currentState : State) (stage : Fin mdp.horizon) (tilt : Real)
    (htilt : |tilt| <= 1) :
    Concentration.HasMGFUpperBoundAt
      (fun head : Action × State =>
        tilt * mdp.transitionResidualHead targetState targetAction targetNextState
            currentState head -
          tilt ^ 2 *
            mdp.transitionCoordinateVariance targetState targetAction targetNextState *
            mdp.transitionVisitHead targetState targetAction currentState head)
      1 0 (policy.actionStateKernel stage currentState) := by
  let Z : Action × State -> Real := fun head =>
    tilt * mdp.transitionResidualHead targetState targetAction targetNextState
        currentState head -
      tilt ^ 2 *
        mdp.transitionCoordinateVariance targetState targetAction targetNextState *
        mdp.transitionVisitHead targetState targetAction currentState head
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
      have h := mdp.transitionResidualHead_variance_compensated_hasMGFUpperBoundAt
        targetState targetAction targetNextState currentState chosenAction tilt htilt
      simpa [ProbabilityTheory.mgf, Z] using h.mgf_le
    have hleft : Integrable
        (fun chosenAction =>
          ∫ nextState, Real.exp (1 * Z (chosenAction, nextState))
            ∂mdp.transition (currentState, chosenAction))
        (policy.actionKernel stage currentState) :=
      integrable_of_fintype _ _ (measurable_of_finite _)
    calc
      (∫ chosenAction,
          ∫ nextState, Real.exp (1 * Z (chosenAction, nextState))
            ∂mdp.transition (currentState, chosenAction)
          ∂policy.actionKernel stage currentState) <=
          ∫ _chosenAction, (1 : Real)
            ∂policy.actionKernel stage currentState := by
              exact integral_mono_ae hleft (integrable_const 1)
                (Filter.Eventually.of_forall (by
                  intro chosenAction
                  simpa only [one_mul] using hinner chosenAction))
      _ = 1 := by simp

omit [Nonempty State] [Nonempty Action] in
/-- The entire generated episode trace has the exact coordinate-variance
compensator, with the compensating count equal to literal visits. -/
theorem trajectoryKernelRemaining_transitionResidual_variance_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (targetState : State) (targetAction : Action) (targetNextState : State)
    (tilt : Real) (htilt : |tilt| <= 1)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (currentState : State) :
    Concentration.HasMGFUpperBoundAt
      (fun trace =>
        tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
            remaining currentState trace -
          tilt ^ 2 *
            mdp.transitionCoordinateVariance targetState targetAction targetNextState *
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
      let variance : Real :=
        mdp.transitionCoordinateVariance targetState targetAction targetNextState
      let Z : StepTrace Action State (remaining + 1) -> Real := fun trace =>
        tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
            (remaining + 1) currentState trace -
          tilt ^ 2 * variance *
            mdp.transitionVisitFrom targetState targetAction
              (remaining + 1) currentState trace
      let Zhead : Action × State -> Real := fun head =>
        tilt * mdp.transitionResidualHead targetState targetAction targetNextState
            currentState head -
          tilt ^ 2 * variance *
            mdp.transitionVisitHead targetState targetAction currentState head
      let Ztail : (Action × State) × StepTrace Action State remaining -> Real :=
        fun p =>
          tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
              remaining p.1.2 p.2 -
            tilt ^ 2 * variance *
              mdp.transitionVisitFrom targetState targetAction remaining p.1.2 p.2
      have hcons : Measurable consStep := StepTrace.measurable_cons remaining
      have hZ : Measurable Z :=
        ((mdp.measurable_transitionResidualFrom targetState targetAction
          targetNextState (remaining + 1)).comp
            (measurable_const.prodMk measurable_id)).const_mul tilt |>.sub
          (((mdp.measurable_transitionVisitFrom targetState targetAction
            (remaining + 1)).comp
              (measurable_const.prodMk measurable_id)).const_mul (tilt ^ 2 * variance))
      have hpair : Integrable (fun p => Real.exp (1 * Z (consStep p)))
          (((policy.actionStateKernel stage).compProd tailKernel) currentState) :=
        integrable_of_fintype _ _ (Real.measurable_exp.comp
          ((hZ.comp hcons).const_mul 1))
      have hhead :=
        mdp.actionStateKernel_transitionResidualHead_variance_compensated_hasMGFUpperBoundAt
          policy targetState targetAction targetNextState currentState stage tilt htilt
      have htail : ∀ head : Action × State,
          Concentration.HasMGFUpperBoundAt
            (fun tail => Ztail (head, tail)) 1 0
            (policy.trajectoryKernelRemaining remaining (by omega) head.2) := by
        intro head
        simpa [Ztail, variance] using ih (by omega) head.2
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
            simp [Z, Zhead, Ztail, consStep, variance, transitionResidualFrom,
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
            simpa [ProbabilityTheory.mgf, Zhead, variance] using hhead.mgf_le

omit [Nonempty State] [Nonempty Action] in
/-- Integrating the random initial state keeps the exact coordinate-variance
compensator on the generated trajectory measure. -/
theorem trajectoryMeasure_transitionResidual_variance_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (targetState : State) (targetAction : Action) (targetNextState : State)
    (tilt : Real) (htilt : |tilt| <= 1) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory =>
        tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
            mdp.horizon trajectory.1 trajectory.2 -
          tilt ^ 2 *
            mdp.transitionCoordinateVariance targetState targetAction targetNextState *
            mdp.transitionVisitFrom targetState targetAction
              mdp.horizon trajectory.1 trajectory.2)
      1 0 (policy.trajectoryMeasure initialState) := by
  let variance : Real :=
    mdp.transitionCoordinateVariance targetState targetAction targetNextState
  let Z : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.transitionResidualFrom targetState targetAction targetNextState
        mdp.horizon trajectory.1 trajectory.2 -
      tilt ^ 2 * variance *
        mdp.transitionVisitFrom targetState targetAction
          mdp.horizon trajectory.1 trajectory.2
  have hZ : Measurable Z :=
    ((mdp.measurable_transitionResidualFrom targetState targetAction
      targetNextState mdp.horizon).const_mul tilt).sub
      ((mdp.measurable_transitionVisitFrom targetState targetAction
        mdp.horizon).const_mul (tilt ^ 2 * variance))
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
      have h :=
        mdp.trajectoryKernelRemaining_transitionResidual_variance_compensated_hasMGFUpperBoundAt
          policy targetState targetAction targetNextState tilt htilt
          mdp.horizon le_rfl state
      simpa [ProbabilityTheory.mgf, Z, variance] using h.mgf_le
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

namespace MarkovPolicy

omit [Nonempty State] [Nonempty Action] in
/-- The exact one-episode batch image of the generated trace inherits the
coordinate-variance MGF. -/
theorem iidEpisodeBatchMeasure_one_aggregateTransitionResidual_variance_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (state : State) (action : Action) (nextState : State)
    (tilt : Real) (htilt : |tilt| <= 1) :
    Concentration.HasMGFUpperBoundAt
      (fun batch : EpisodeBatch mdp 1 =>
        tilt * batch.aggregateTransitionResidual state action nextState -
          tilt ^ 2 * mdp.transitionCoordinateVariance state action nextState *
            batch.aggregateVisitReal state action)
      1 0 (policy.iidEpisodeBatchMeasure initialState 1) := by
  let variance : Real := mdp.transitionCoordinateVariance state action nextState
  let Ztrace : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.transitionResidualFrom state action nextState
        mdp.horizon trajectory.1 trajectory.2 -
      tilt ^ 2 * variance *
        mdp.transitionVisitFrom state action mdp.horizon trajectory.1 trajectory.2
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionResidual state action nextState -
      tilt ^ 2 * variance * batch.aggregateVisitReal state action
  let eval0 : (Fin 1 -> State × StepTrace Action State mdp.horizon) ->
      State × StepTrace Action State mdp.horizon := Function.eval 0
  let batchMap := mdp.episodeBatchOfTrajectories 1
  have htrace :=
    mdp.trajectoryMeasure_transitionResidual_variance_compensated_hasMGFUpperBoundAt
      policy initialState state action nextState tilt htilt
  have hfamilyMap : Concentration.HasMGFUpperBoundAt Ztrace 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map eval0) := by
    rw [policy.iidTrajectoryFamilyMeasure_map_eval initialState (0 : Fin 1)]
    exact htrace
  have hfamily : Concentration.HasMGFUpperBoundAt (Ztrace ∘ eval0) 1 0
      (policy.iidTrajectoryFamilyMeasure initialState 1) :=
    Concentration.HasMGFUpperBoundAt.of_map
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
      apply hfamily.integrable_exp_mul s |>.congr
      exact Filter.Eventually.of_forall fun trajectories => by
        simp only [Function.comp_apply]
        rw [hpoint trajectories]
    · rw [ProbabilityTheory.mgf_congr
        (Filter.Eventually.of_forall fun trajectories => by
          simp only [Function.comp_apply]
          exact hpoint trajectories)]
      exact hfamily.mgf_le
  have hbatchMeas : Measurable batchMap :=
    mdp.measurable_episodeBatchOfTrajectories 1
  have hZbatchMeas : Measurable Zbatch :=
    (EpisodeBatch.measurable_aggregateTransitionResidual state action nextState
      |>.const_mul tilt).sub
      (EpisodeBatch.measurable_aggregateVisitReal state action |>.const_mul
        (tilt ^ 2 * variance))
  have hid : Concentration.HasMGFUpperBoundAt id 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map
        (Zbatch ∘ batchMap)) :=
    (Concentration.HasMGFUpperBoundAt.id_map_iff
      (hZbatchMeas.comp hbatchMeas).aemeasurable).2 hcomposed
  unfold iidEpisodeBatchMeasure
  apply (Concentration.HasMGFUpperBoundAt.id_map_iff hZbatchMeas.aemeasurable).1
  rw [Measure.map_map hZbatchMeas hbatchMeas]
  exact hid

end MarkovPolicy

namespace AdaptiveEpisodeBatchSource

/-- Every successor episode in the recurrent generated process inherits the
same coordinate-variance compensated conditional MGF. -/
theorem aggregateTransitionResidual_succ_variance_compensated_hasCondMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (n : Nat) (tilt : Real) (htilt : |tilt| <= 1) :
    Concentration.HasCondMGFUpperBoundAt (mΩ := MeasurableSpace.pi)
      (batchPrefixFiltration (mdp := mdp) 1 n)
      ((batchPrefixFiltration (mdp := mdp) 1).le n)
      (fun trajectory =>
        tilt * source.aggregateTransitionResidualIncrement
            state action nextState (n + 1) trajectory -
          tilt ^ 2 * mdp.transitionCoordinateVariance state action nextState *
            source.aggregateVisitIncrement state action (n + 1) trajectory)
      1 0 source.trajectoryMeasure := by
  let prefixMap : EpisodeBatchTrajectory mdp 1 -> EpisodeBatchPrefix mdp 1 n :=
    Preorder.frestrictLe n
  let variance : Real := mdp.transitionCoordinateVariance state action nextState
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionResidual state action nextState -
      tilt ^ 2 * variance * batch.aggregateVisitReal state action
  have hZbatch : Measurable Zbatch :=
    (EpisodeBatch.measurable_aggregateTransitionResidual state action nextState
      |>.const_mul tilt).sub
      (EpisodeBatch.measurable_aggregateVisitReal state action |>.const_mul
        (tilt ^ 2 * variance))
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
        policy.iidEpisodeBatchMeasure_one_aggregateTransitionResidual_variance_compensated_hasMGFUpperBoundAt
          initialState state action nextState tilt htilt
      have hbatch' : Concentration.HasMGFUpperBoundAt Zbatch 1 0
          (source.batchKernel n history) := by
        rw [source.batchKernel_eq_iidEpisodeBatchMeasure n history]
        simpa [Zbatch, variance] using hbatch
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
    simpa [Zbatch, variance, aggregateTransitionResidualIncrement,
      aggregateTransitionResidualPrefix, aggregateVisitIncrement,
      aggregateVisitPrefix, Preorder.frestrictLe_apply] using
      source.integrable_exp_mul_aggregateTransitionResidual_compensatedIncrement
        state action nextState (n + 1) tilt (tilt ^ 2 * variance) s
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
  simpa [Zbatch, variance, aggregateTransitionResidualIncrement,
    aggregateTransitionResidualPrefix, aggregateVisitIncrement,
    aggregateVisitPrefix, Preorder.frestrictLe_apply] using hcomap

/-- Coordinate zero has the same exact coordinate-variance certificate under
the initial marginal of the generated recurrent trajectory. -/
theorem aggregateTransitionResidual_zero_variance_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (tilt : Real) (htilt : |tilt| <= 1) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        tilt * source.aggregateTransitionResidualIncrement
            state action nextState 0 trajectory -
          tilt ^ 2 * mdp.transitionCoordinateVariance state action nextState *
            source.aggregateVisitIncrement state action 0 trajectory)
      1 0 source.trajectoryMeasure := by
  let variance : Real := mdp.transitionCoordinateVariance state action nextState
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionResidual state action nextState -
      tilt ^ 2 * variance * batch.aggregateVisitReal state action
  have hbatch : Concentration.HasMGFUpperBoundAt Zbatch 1 0
      (source.initialPolicy.iidEpisodeBatchMeasure initialState 1) := by
    simpa [Zbatch, variance] using
      source.initialPolicy.iidEpisodeBatchMeasure_one_aggregateTransitionResidual_variance_compensated_hasMGFUpperBoundAt
        initialState state action nextState tilt htilt
  rw [← source.trajectoryMeasure_map_eval_zero] at hbatch
  have hlift := Concentration.HasMGFUpperBoundAt.of_map
    (X := Zbatch)
    (Z := fun trajectory : EpisodeBatchTrajectory mdp 1 => trajectory 0)
    (measurable_pi_apply 0).aemeasurable hbatch
  simpa [Zbatch, variance, aggregateTransitionResidualIncrement,
    aggregateTransitionResidualPrefix, aggregateVisitIncrement,
    aggregateVisitPrefix, Preorder.frestrictLe_apply] using hlift

/-- Fixed-tilt actual-count upper tail with the true transition-coordinate
variance. -/
theorem measure_aggregateTransitionResidualSum_ge_inter_visitSum_le_variance
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (rounds : Nat) (tilt threshold visitBudget : Real)
    (htilt : 0 < tilt) (htilt_le : tilt <= 1) :
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
        (Real.exp (-tilt * threshold +
          tilt ^ 2 * mdp.transitionCoordinateVariance state action nextState *
            visitBudget)) := by
  let F := batchPrefixFiltration (mdp := mdp) 1
  let variance : Real := mdp.transitionCoordinateVariance state action nextState
  let Y : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    source.aggregateTransitionResidualIncrement state action nextState i trajectory
  let V : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    source.aggregateVisitIncrement state action i trajectory
  let Z : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    tilt * Y i trajectory - tilt ^ 2 * variance * V i trajectory
  have htiltAbs : |tilt| <= 1 := by rw [abs_of_pos htilt]; exact htilt_le
  have hadapted : StronglyAdapted F Z := by
    simpa [F, Y, V, Z, variance] using
      source.aggregateTransitionResidual_compensated_stronglyAdapted_piLE
        state action nextState tilt (tilt ^ 2 * variance)
  have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 0
      source.trajectoryMeasure := by
    simpa [Y, V, Z, variance] using
      source.aggregateTransitionResidual_zero_variance_compensated_hasMGFUpperBoundAt
        state action nextState tilt htiltAbs
  have hsucc : ∀ i, i < rounds - 1 ->
      Concentration.HasCondMGFUpperBoundAt
        (F i) (F.le i) (Z (i + 1)) 1 0 source.trajectoryMeasure := by
    intro i _hi
    simpa [F, Y, V, Z, variance] using
      source.aggregateTransitionResidual_succ_variance_compensated_hasCondMGFUpperBoundAt
        state action nextState i tilt htiltAbs
  simpa [Y, V, variance] using
    (Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
      (μ := source.trajectoryMeasure) (ℱ := F) Y V rounds tilt
      (tilt ^ 2 * variance) threshold visitBudget hadapted hzero hsucc htilt.le
      (mul_nonneg (sq_nonneg tilt) (mdp.transitionCoordinateVariance_nonneg
        state action nextState)))

/-- Two-sided coordinate-variance prefix tail on the same generated law. -/
theorem measure_abs_aggregateTransitionResidualSum_ge_inter_visitSum_le_variance
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (state : State) (action : Action) (nextState : State)
    (rounds : Nat) (tilt threshold visitBudget : Real)
    (htilt : 0 < tilt) (htilt_le : tilt <= 1) :
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
        (Real.exp (-tilt * threshold +
          tilt ^ 2 * mdp.transitionCoordinateVariance state action nextState *
            visitBudget)) := by
  let variance : Real := mdp.transitionCoordinateVariance state action nextState
  let positive : Set (EpisodeBatchTrajectory mdp 1) :=
    {trajectory |
      threshold <= ∑ i ∈ Finset.range rounds,
        source.aggregateTransitionResidualIncrement state action nextState i trajectory ∧
      (∑ i ∈ Finset.range rounds,
        source.aggregateVisitIncrement state action i trajectory) <= visitBudget}
  let negative : Set (EpisodeBatchTrajectory mdp 1) :=
    {trajectory |
      threshold <= ∑ i ∈ Finset.range rounds,
        -source.aggregateTransitionResidualIncrement state action nextState i trajectory ∧
      (∑ i ∈ Finset.range rounds,
        source.aggregateVisitIncrement state action i trajectory) <= visitBudget}
  have hpos := source.measure_aggregateTransitionResidualSum_ge_inter_visitSum_le_variance
    state action nextState rounds tilt threshold visitBudget htilt htilt_le
  have hneg : source.trajectoryMeasure negative <=
      ENNReal.ofReal (Real.exp (-tilt * threshold +
        tilt ^ 2 * variance * visitBudget)) := by
    let F := batchPrefixFiltration (mdp := mdp) 1
    let Y : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      -source.aggregateTransitionResidualIncrement state action nextState i trajectory
    let V : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      source.aggregateVisitIncrement state action i trajectory
    let Z : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      tilt * Y i trajectory - tilt ^ 2 * variance * V i trajectory
    have htiltAbs : |tilt| <= 1 := by rw [abs_of_pos htilt]; exact htilt_le
    have hnegTiltAbs : |-tilt| <= 1 := by simpa using htiltAbs
    have hadapted : StronglyAdapted F Z := by
      have h := source.aggregateTransitionResidual_compensated_stronglyAdapted_piLE
        state action nextState (-tilt) ((-tilt) ^ 2 * variance)
      simpa [F, Y, V, Z] using h
    have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 0
        source.trajectoryMeasure := by
      have h :=
        source.aggregateTransitionResidual_zero_variance_compensated_hasMGFUpperBoundAt
          state action nextState (-tilt) hnegTiltAbs
      simpa [Y, V, Z, variance] using h
    have hsucc : ∀ i, i < rounds - 1 ->
        Concentration.HasCondMGFUpperBoundAt
          (F i) (F.le i) (Z (i + 1)) 1 0 source.trajectoryMeasure := by
      intro i _hi
      have h :=
        source.aggregateTransitionResidual_succ_variance_compensated_hasCondMGFUpperBoundAt
          state action nextState i (-tilt) hnegTiltAbs
      simpa [F, Y, V, Z, variance] using h
    simpa [negative, Y, V, variance] using
      (Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
        (μ := source.trajectoryMeasure) (ℱ := F) Y V rounds tilt
        (tilt ^ 2 * variance) threshold visitBudget hadapted hzero hsucc htilt.le
        (mul_nonneg (sq_nonneg tilt) (mdp.transitionCoordinateVariance_nonneg
          state action nextState)))
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
    · left; exact ⟨hpos', hvis⟩
    · right
      refine ⟨?_, hvis⟩
      simpa [negative, Finset.sum_neg_distrib] using hneg'
  calc
    source.trajectoryMeasure _ <= source.trajectoryMeasure (positive ∪ negative) :=
      measure_mono hsubset
    _ <= source.trajectoryMeasure positive + source.trajectoryMeasure negative :=
      measure_union_le _ _
    _ <= ENNReal.ofReal (Real.exp (-tilt * threshold +
          tilt ^ 2 * variance * visitBudget)) +
        ENNReal.ofReal (Real.exp (-tilt * threshold +
          tilt ^ 2 * variance * visitBudget)) :=
      add_le_add (by simpa [positive, variance] using hpos) hneg
    _ = 2 * ENNReal.ofReal (Real.exp (-tilt * threshold +
          tilt ^ 2 * variance * visitBudget)) := by ring

end AdaptiveEpisodeBatchSource

end BanditRLProof.FiniteHorizonRL
