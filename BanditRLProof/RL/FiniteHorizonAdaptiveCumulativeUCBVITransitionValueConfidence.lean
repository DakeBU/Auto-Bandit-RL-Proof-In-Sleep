import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIBernsteinConfidence
import BanditRLProof.RL.FiniteHorizonStochasticRewardBellmanInnovationConcentration
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Same-source bounded transition-functional probes for UCBVI-CH

Singleton transition coordinates do not by themselves imply a sharp bound for
`(P_hat - P) V*` without a `sqrt |State|` loss.  This module therefore proves
the bounded scalar projection as another coordinate of the same generated
transition residual family.  It never introduces an offline or independent
sample law.
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

/-- The normalized optimal continuation-value probe used by the sharp
transition-value confidence coordinate.  The symmetric shift avoids requiring
nonnegativity merely to apply Hoeffding. -/
noncomputable def optimalTailProbe
    (mdp : MDP State Action) (stage : Fin mdp.horizon) (nextState : State) : Real :=
  (mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt) nextState +
      (mdp.horizon : Real)) /
    (2 * (mdp.horizon : Real))

/-- Under rewards in `[-1,1]`, the normalized optimal tail is in `[0,1]`. -/
theorem optimalTailProbe_mem_Icc
    (mdp : MDP State Action)
    (hreward : ∀ state action, |mdp.reward state action| <= 1)
    (stage : Fin mdp.horizon) (nextState : State) :
    mdp.optimalTailProbe stage nextState ∈ Set.Icc (0 : Real) 1 := by
  have hhorizon : 0 < (mdp.horizon : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (by
      intro hzero
      have : stage.val < 0 := by simpa [hzero] using stage.isLt
      omega))
  have hvalue :
      |mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt) nextState| <=
        (mdp.horizon : Real) := by
    rw [← mdp.optimalPolicy_valueAt_eq_optimalValueAt]
    unfold MarkovPolicy.valueAt
    have hremaining := mdp.optimalPolicy.valueRemaining_abs_le_of_rewardBound
      (1 : NNReal) (by simpa using hreward)
      (mdp.horizon - (stage + 1)) (Nat.sub_le _ _) nextState
    calc
      |mdp.optimalPolicy.valueRemaining (mdp.horizon - (stage + 1))
          (Nat.sub_le _ _) nextState| <=
          ((mdp.horizon - (stage + 1) : Nat) : Real) := by simpa using hremaining
      _ <= (mdp.horizon : Real) := by exact_mod_cast Nat.sub_le _ _
  rw [abs_le] at hvalue
  constructor
  · unfold optimalTailProbe
    exact div_nonneg (by linarith [hvalue.1]) (by positivity)
  · unfold optimalTailProbe
    apply (div_le_one (by positivity)).2
    linarith [hvalue.2]

/-- Linear transition residual for a fixed bounded probe.  Writing it as the
finite linear combination of singleton residuals makes its relation to the
coordinate event explicit. -/
noncomputable def transitionFunctionalResidualHead
    (mdp : MDP State Action) (feature : State -> Real)
    (targetState : State) (targetAction : Action)
    (currentState : State) (head : Action × State) : Real :=
  ∑ nextState : State, feature nextState *
    mdp.transitionResidualHead targetState targetAction nextState currentState head

/-- The same linear probe on a remaining generated trace. -/
noncomputable def transitionFunctionalResidualFrom
    (mdp : MDP State Action) (feature : State -> Real)
    (targetState : State) (targetAction : Action)
    (remaining : Nat) (currentState : State)
    (trace : StepTrace Action State remaining) : Real :=
  ∑ nextState : State, feature nextState *
    mdp.transitionResidualFrom targetState targetAction nextState
      remaining currentState trace

omit [Nonempty State] [Nonempty Action] in
theorem measurable_transitionFunctionalResidualFrom
    (mdp : MDP State Action) (feature : State -> Real)
    (targetState : State) (targetAction : Action) (remaining : Nat) :
    Measurable (fun p : State × StepTrace Action State remaining =>
      mdp.transitionFunctionalResidualFrom feature targetState targetAction
        remaining p.1 p.2) := by
  unfold transitionFunctionalResidualFrom
  exact Finset.measurable_sum Finset.univ fun nextState _ =>
    (mdp.measurable_transitionResidualFrom targetState targetAction
      nextState remaining).const_mul (feature nextState)

omit [Nonempty State] [Nonempty Action] in
/-- A finite-state transition integral is its finite singleton-mass sum. -/
theorem transitionValue_eq_sum_measureReal
    (mdp : MDP State Action) (feature : State -> Real)
    (state : State) (action : Action) :
    mdp.transitionValue feature state action =
      ∑ nextState : State,
        feature nextState * (mdp.transition (state, action)).real {nextState} := by
  unfold transitionValue
  have hint : Integrable feature (mdp.transition (state, action)) :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  rw [integral_countable hint, tsum_fintype]
  apply Finset.sum_congr rfl
  intro nextState _
  simp [smul_eq_mul, mul_comm]

omit [Nonempty State] [Nonempty Action] in
/-- On a visited cell, the linear coordinate residual is exactly the centered
bounded feature; away from the cell it is zero. -/
theorem transitionFunctionalResidualHead_eq
    (mdp : MDP State Action) (feature : State -> Real)
    (targetState : State) (targetAction : Action)
    (currentState : State) (head : Action × State) :
    mdp.transitionFunctionalResidualHead feature targetState targetAction
        currentState head =
      if currentState = targetState ∧ head.1 = targetAction then
        feature head.2 - mdp.transitionValue feature targetState targetAction
      else 0 := by
  classical
  unfold transitionFunctionalResidualHead transitionResidualHead
  by_cases hvisit : currentState = targetState ∧ head.1 = targetAction
  · rw [if_pos hvisit]
    simp only [if_pos hvisit]
    have hmass := mdp.transitionValue_eq_sum_measureReal
      feature targetState targetAction
    rw [hmass]
    have hsingle :
        (∑ nextState : State,
          feature nextState * (if head.2 = nextState then 1 else 0)) =
          feature head.2 := by
      classical
      simp [eq_comm]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsingle]
  · rw [if_neg hvisit]
    simp [hvisit]

omit [Nonempty State] [Nonempty Action] in
/-- The linear probe obeys the same chronological recursion as every singleton
coordinate. -/
theorem transitionFunctionalResidualFrom_succ
    (mdp : MDP State Action) (feature : State -> Real)
    (targetState : State) (targetAction : Action)
    (remaining : Nat) (currentState : State)
    (trace : StepTrace Action State (remaining + 1)) :
    mdp.transitionFunctionalResidualFrom feature targetState targetAction
        (remaining + 1) currentState trace =
      mdp.transitionFunctionalResidualHead feature targetState targetAction
          currentState (trace 0) +
        mdp.transitionFunctionalResidualFrom feature targetState targetAction
          remaining (trace 0).2 (Fin.tail trace) := by
  classical
  unfold transitionFunctionalResidualFrom transitionFunctionalResidualHead
  simp_rw [transitionResidualFrom, mul_add]
  rw [Finset.sum_add_distrib]

omit [Nonempty State] [Nonempty Action] in
/-- A `[0,1]` probe has the standard Hoeffding compensated MGF on one true
transition draw. -/
theorem transitionFunctionalResidualHead_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (targetState : State) (targetAction : Action)
    (currentState : State) (chosenAction : Action) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun nextState =>
        tilt * mdp.transitionFunctionalResidualHead feature targetState targetAction
            currentState (chosenAction, nextState) -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitHead targetState targetAction
              currentState (chosenAction, nextState))
      1 0 (mdp.transition (currentState, chosenAction)) := by
  by_cases hvisit : currentState = targetState ∧ chosenAction = targetAction
  · have hmean :
        (∫ nextState, feature nextState
          ∂mdp.transition (currentState, chosenAction)) =
          mdp.transitionValue feature targetState targetAction := by
      rw [hvisit.1, hvisit.2]
      rfl
    have hsub :=
      Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mdp.transition (currentState, chosenAction))
        (measurable_of_finite feature).aemeasurable
        (Filter.Eventually.of_forall hfeature) hmean
    have hproxy :
        (((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)) =
          (1 / 4 : Real) := by
      simp [Concentration.intervalVarianceProxy]
      norm_num
    have hfixed : Concentration.HasMGFUpperBoundAt
        (fun nextState =>
          feature nextState - mdp.transitionValue feature targetState targetAction)
        tilt (tilt ^ 2 / 8) (mdp.transition (currentState, chosenAction)) := by
      constructor
      · exact hsub.integrable_exp_mul
      · have h := hsub.mgf_le tilt
        rw [hproxy] at h
        convert h using 1 <;> ring
    have hcomp := hfixed.compensated
    convert hcomp using 1
    funext nextState
    rw [mdp.transitionFunctionalResidualHead_eq]
    simp [hvisit, transitionVisitHead]
  · have hzero : Concentration.HasMGFUpperBoundAt
        (fun _nextState : State => (0 : Real)) 1 0
        (mdp.transition (currentState, chosenAction)) := by
      constructor
      · intro s
        simpa using (integrable_const
          (μ := mdp.transition (currentState, chosenAction)) (Real.exp (s * 0)))
      · simp [ProbabilityTheory.mgf]
    convert hzero using 1
    funext nextState
    rw [mdp.transitionFunctionalResidualHead_eq]
    simp [hvisit, transitionVisitHead]

omit [Nonempty State] [Nonempty Action] in
theorem actionStateKernel_transitionFunctionalResidualHead_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (targetState : State) (targetAction : Action)
    (currentState : State) (stage : Fin mdp.horizon) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun head : Action × State =>
        tilt * mdp.transitionFunctionalResidualHead feature targetState targetAction
            currentState head -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitHead targetState targetAction currentState head)
      1 0 (policy.actionStateKernel stage currentState) := by
  let Z : Action × State -> Real := fun head =>
    tilt * mdp.transitionFunctionalResidualHead feature targetState targetAction
        currentState head -
      (tilt ^ 2 / 8) *
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
      have h := mdp.transitionFunctionalResidualHead_compensated_hasMGFUpperBoundAt
        feature hfeature targetState targetAction currentState chosenAction tilt
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
theorem trajectoryKernelRemaining_transitionFunctionalResidual_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (targetState : State) (targetAction : Action) (tilt : Real)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (currentState : State) :
    Concentration.HasMGFUpperBoundAt
      (fun trace =>
        tilt * mdp.transitionFunctionalResidualFrom feature targetState targetAction
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
      simpa [transitionFunctionalResidualFrom, transitionResidualFrom,
        transitionVisitFrom] using hzero
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
        tilt * mdp.transitionFunctionalResidualFrom feature targetState targetAction
            (remaining + 1) currentState trace -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitFrom targetState targetAction
              (remaining + 1) currentState trace
      let Zhead : Action × State -> Real := fun head =>
        tilt * mdp.transitionFunctionalResidualHead feature targetState targetAction
            currentState head -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitHead targetState targetAction currentState head
      let Ztail : (Action × State) × StepTrace Action State remaining -> Real :=
        fun p =>
          tilt * mdp.transitionFunctionalResidualFrom feature targetState targetAction
              remaining p.1.2 p.2 -
            (tilt ^ 2 / 8) *
              mdp.transitionVisitFrom targetState targetAction remaining p.1.2 p.2
      have hcons : Measurable consStep := StepTrace.measurable_cons remaining
      have hZ : Measurable Z :=
        ((mdp.measurable_transitionFunctionalResidualFrom feature targetState
          targetAction (remaining + 1)).comp
            (measurable_const.prodMk measurable_id)).const_mul tilt |>.sub
          (((mdp.measurable_transitionVisitFrom targetState targetAction
            (remaining + 1)).comp
              (measurable_const.prodMk measurable_id)).const_mul (tilt ^ 2 / 8))
      have hpair : Integrable (fun p => Real.exp (1 * Z (consStep p)))
          (((policy.actionStateKernel stage).compProd tailKernel) currentState) :=
        integrable_of_fintype _ _ (Real.measurable_exp.comp
          ((hZ.comp hcons).const_mul 1))
      have hhead :=
        mdp.actionStateKernel_transitionFunctionalResidualHead_compensated_hasMGFUpperBoundAt
          policy feature hfeature targetState targetAction currentState stage tilt
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
            simp only [Z, Zhead, Ztail, consStep]
            rw [mdp.transitionFunctionalResidualFrom_succ]
            simp [transitionVisitFrom]
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
theorem trajectoryMeasure_transitionFunctionalResidual_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (targetState : State) (targetAction : Action) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory =>
        tilt * mdp.transitionFunctionalResidualFrom feature targetState targetAction
            mdp.horizon trajectory.1 trajectory.2 -
          (tilt ^ 2 / 8) *
            mdp.transitionVisitFrom targetState targetAction
              mdp.horizon trajectory.1 trajectory.2)
      1 0 (policy.trajectoryMeasure initialState) := by
  let Z : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.transitionFunctionalResidualFrom feature targetState targetAction
        mdp.horizon trajectory.1 trajectory.2 -
      (tilt ^ 2 / 8) * mdp.transitionVisitFrom targetState targetAction
        mdp.horizon trajectory.1 trajectory.2
  have hZ : Measurable Z :=
    ((mdp.measurable_transitionFunctionalResidualFrom feature targetState
      targetAction mdp.horizon).const_mul tilt).sub
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
      have h :=
        mdp.trajectoryKernelRemaining_transitionFunctionalResidual_compensated_hasMGFUpperBoundAt
          policy feature hfeature targetState targetAction tilt mdp.horizon le_rfl state
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

omit [Nonempty State] [Nonempty Action] in
theorem transitionFunctionalResidualFrom_eq_aggregateFunctionalResidual
    (mdp : MDP State Action) (feature : State -> Real)
    (targetState : State) (targetAction : Action)
    (trajectory : State × StepTrace Action State mdp.horizon) :
    mdp.transitionFunctionalResidualFrom feature targetState targetAction
        mdp.horizon trajectory.1 trajectory.2 =
      ∑ nextState : State, feature nextState *
        EpisodeBatch.aggregateTransitionResidual
          (mdp.episodeBatchOfTrajectories 1 (fun _ => trajectory))
          targetState targetAction nextState := by
  classical
  unfold transitionFunctionalResidualFrom EpisodeBatch.aggregateTransitionResidual
  apply Finset.sum_congr rfl
  intro nextState _
  rw [mdp.transitionResidualFrom_eq_aggregateCounts
    targetState targetAction nextState trajectory]

end MDP

namespace EpisodeBatch

/-- A bounded transition functional is another finite coordinate of the same
aggregate singleton-residual table. -/
noncomputable def aggregateTransitionFunctionalResidual
    {mdp : MDP State Action} (batch : EpisodeBatch mdp 1)
    (feature : State -> Real) (state : State) (action : Action) : Real :=
  ∑ nextState : State, feature nextState *
    batch.aggregateTransitionResidual state action nextState

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateTransitionFunctionalResidual
    {mdp : MDP State Action} (feature : State -> Real)
    (state : State) (action : Action) :
    Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.aggregateTransitionFunctionalResidual feature state action) := by
  unfold aggregateTransitionFunctionalResidual
  exact Finset.measurable_sum Finset.univ fun nextState _ =>
    (measurable_aggregateTransitionResidual state action nextState
      |>.const_mul (feature nextState))

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem abs_aggregateTransitionFunctionalResidual_le
    {mdp : MDP State Action} (batch : EpisodeBatch mdp 1)
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (state : State) (action : Action) :
    |batch.aggregateTransitionFunctionalResidual feature state action| <=
      2 * Fintype.card State * (mdp.horizon : Real) := by
  classical
  unfold aggregateTransitionFunctionalResidual
  calc
    |∑ nextState : State,
        feature nextState * batch.aggregateTransitionResidual
          state action nextState| <=
        ∑ nextState : State,
          |feature nextState * batch.aggregateTransitionResidual
            state action nextState| := Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _nextState : State, 2 * (mdp.horizon : Real) := by
      apply Finset.sum_le_sum
      intro nextState _
      rw [abs_mul]
      have hfabs : |feature nextState| <= 1 := by
        rw [abs_le]
        constructor <;> linarith [hfeature nextState |>.1, hfeature nextState |>.2]
      calc
        |feature nextState| *
            |batch.aggregateTransitionResidual state action nextState| <=
            1 * (2 * (mdp.horizon : Real)) :=
          mul_le_mul hfabs
            (batch.abs_aggregateTransitionResidual_le_two_mul_horizon
              state action nextState) (abs_nonneg _) (by norm_num)
        _ = 2 * (mdp.horizon : Real) := by ring
    _ = 2 * Fintype.card State * (mdp.horizon : Real) := by
      simp
      ring

end EpisodeBatch

namespace TransitionCountSummary

/-- At a positive pooled count, empirical transition integration is the exact
normalized finite count sum. -/
theorem integral_aggregateEmpiricalTransitionKernel_eq_sum_div
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (feature : State -> Real)
    (state : State) (action : Action)
    (hpos : 0 < summary.aggregateVisitCount state action) :
    (∫ nextState, feature nextState
      ∂summary.aggregateEmpiricalTransitionKernel defaultState (state, action)) =
      (∑ nextState : State,
        feature nextState *
          (summary.aggregateTransitionCount state action nextState : Real)) /
        (summary.aggregateVisitCount state action : Real) := by
  change (∫ nextState, feature nextState
      ∂(summary.aggregateEmpiricalTransitionPMF
        defaultState state action).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp_rw [aggregateEmpiricalTransitionPMF_apply_of_aggregateVisitCount_pos
    summary defaultState state action _ hpos]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, smul_eq_mul]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro nextState _
  ring

end TransitionCountSummary

namespace MarkovPolicy

omit [Nonempty State] [Nonempty Action] in
theorem iidEpisodeBatchMeasure_one_aggregateTransitionFunctionalResidual_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (state : State) (action : Action) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun batch : EpisodeBatch mdp 1 =>
        tilt * batch.aggregateTransitionFunctionalResidual feature state action -
          (tilt ^ 2 / 8) * batch.aggregateVisitReal state action)
      1 0 (policy.iidEpisodeBatchMeasure initialState 1) := by
  let Ztrace : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.transitionFunctionalResidualFrom feature state action
        mdp.horizon trajectory.1 trajectory.2 -
      (tilt ^ 2 / 8) *
        mdp.transitionVisitFrom state action mdp.horizon trajectory.1 trajectory.2
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionFunctionalResidual feature state action -
      (tilt ^ 2 / 8) * batch.aggregateVisitReal state action
  let eval0 : (Fin 1 -> State × StepTrace Action State mdp.horizon) ->
      State × StepTrace Action State mdp.horizon := Function.eval 0
  let batchMap := mdp.episodeBatchOfTrajectories 1
  have htrace :=
    mdp.trajectoryMeasure_transitionFunctionalResidual_compensated_hasMGFUpperBoundAt
      policy initialState feature hfeature state action tilt
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
    have hfunctional :=
      mdp.transitionFunctionalResidualFrom_eq_aggregateFunctionalResidual
        feature state action (trajectories 0)
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
      EpisodeBatch.aggregateTransitionFunctionalResidual,
      EpisodeBatch.aggregateVisitReal]
    rw [← hfunctional, ← hvisit]
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
    (EpisodeBatch.measurable_aggregateTransitionFunctionalResidual
      feature state action |>.const_mul tilt).sub
      (EpisodeBatch.measurable_aggregateVisitReal state action
        |>.const_mul (tilt ^ 2 / 8))
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

/-- Fixed-round functional residual read from the actual generated batch. -/
noncomputable def aggregateTransitionFunctionalResidualPrefix
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real) (state : State) (action : Action)
    (round : Nat) (history : EpisodeBatchPrefix mdp 1 round) : Real :=
  EpisodeBatch.aggregateTransitionFunctionalResidual
    (history ⟨round, Finset.mem_Iic.mpr le_rfl⟩) feature state action

noncomputable def aggregateTransitionFunctionalResidualIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real) (state : State) (action : Action)
    (round : Nat) (trajectory : EpisodeBatchTrajectory mdp 1) : Real :=
  source.aggregateTransitionFunctionalResidualPrefix
    feature state action round (Preorder.frestrictLe round trajectory)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateTransitionFunctionalResidualPrefix
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real) (state : State) (action : Action)
    (round : Nat) :
    Measurable (source.aggregateTransitionFunctionalResidualPrefix
      feature state action round) := by
  exact (EpisodeBatch.measurable_aggregateTransitionFunctionalResidual
    feature state action).comp
    (measurable_pi_apply
      (⟨round, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic round))

omit [Nonempty State] [Nonempty Action] in
theorem measurable_aggregateTransitionFunctionalResidualIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real) (state : State) (action : Action)
    (round : Nat) :
    Measurable (source.aggregateTransitionFunctionalResidualIncrement
      feature state action round) := by
  exact (source.measurable_aggregateTransitionFunctionalResidualPrefix
    feature state action round).comp (Preorder.measurable_frestrictLe round)

omit [Nonempty State] [Nonempty Action] in
theorem aggregateTransitionFunctionalResidual_compensated_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real) (state : State) (action : Action)
    (tilt varianceCoeff : Real) :
    StronglyAdapted (batchPrefixFiltration (mdp := mdp) 1)
      (fun round trajectory =>
        tilt * source.aggregateTransitionFunctionalResidualIncrement
            feature state action round trajectory -
          varianceCoeff * source.aggregateVisitIncrement
            state action round trajectory) := by
  intro round
  have hprefix : Measurable (fun history : EpisodeBatchPrefix mdp 1 round =>
      tilt * source.aggregateTransitionFunctionalResidualPrefix
          feature state action round history -
        varianceCoeff * source.aggregateVisitPrefix
          state action round history) :=
    (source.measurable_aggregateTransitionFunctionalResidualPrefix
      feature state action round |>.const_mul tilt).sub
      (source.measurable_aggregateVisitPrefix state action round
        |>.const_mul varianceCoeff)
  exact (hprefix.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

omit [Nonempty State] [Nonempty Action] in
theorem integrable_exp_mul_aggregateTransitionFunctionalResidual_compensatedIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (state : State) (action : Action)
    (round : Nat) (tilt varianceCoeff s : Real) :
    Integrable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      Real.exp (s *
        (tilt * source.aggregateTransitionFunctionalResidualIncrement
            feature state action round trajectory -
          varianceCoeff * source.aggregateVisitIncrement
            state action round trajectory))) source.trajectoryMeasure := by
  let X := fun trajectory : EpisodeBatchTrajectory mdp 1 =>
    tilt * source.aggregateTransitionFunctionalResidualIncrement
        feature state action round trajectory -
      varianceCoeff * source.aggregateVisitIncrement state action round trajectory
  have hX : Measurable X :=
    (source.measurable_aggregateTransitionFunctionalResidualIncrement
      feature state action round |>.const_mul tilt).sub
      (source.measurable_aggregateVisitIncrement state action round
        |>.const_mul varianceCoeff)
  let bound := |tilt| *
      (2 * Fintype.card State * (mdp.horizon : Real)) +
    |varianceCoeff| * (mdp.horizon : Real)
  have hbound : ∀ trajectory : EpisodeBatchTrajectory mdp 1,
      |X trajectory| <= bound := by
    intro trajectory
    have hres := (trajectory round)
      |>.abs_aggregateTransitionFunctionalResidual_le feature hfeature state action
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
          |tilt * source.aggregateTransitionFunctionalResidualIncrement
              feature state action round trajectory| +
            |varianceCoeff * source.aggregateVisitIncrement
              state action round trajectory| := abs_sub _ _
      _ = |tilt| *
            |source.aggregateTransitionFunctionalResidualIncrement
              feature state action round trajectory| +
          |varianceCoeff| *
            |source.aggregateVisitIncrement state action round trajectory| := by
          rw [abs_mul, abs_mul]
      _ <= bound := by
        have hres' :
            |source.aggregateTransitionFunctionalResidualIncrement
              feature state action round trajectory| <=
              2 * Fintype.card State * (mdp.horizon : Real) := by
          simpa [aggregateTransitionFunctionalResidualIncrement,
            aggregateTransitionFunctionalResidualPrefix] using hres
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
    ((Real.continuous_exp.measurable.comp
      (measurable_const.mul hX)).aestronglyMeasurable)
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

theorem aggregateTransitionFunctionalResidual_succ_compensated_hasCondMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (state : State) (action : Action) (n : Nat) (tilt : Real) :
    Concentration.HasCondMGFUpperBoundAt (mΩ := MeasurableSpace.pi)
      (batchPrefixFiltration (mdp := mdp) 1 n)
      ((batchPrefixFiltration (mdp := mdp) 1).le n)
      (fun trajectory =>
        tilt * source.aggregateTransitionFunctionalResidualIncrement
            feature state action (n + 1) trajectory -
          (tilt ^ 2 / 8) * source.aggregateVisitIncrement
            state action (n + 1) trajectory)
      1 0 source.trajectoryMeasure := by
  let prefixMap : EpisodeBatchTrajectory mdp 1 -> EpisodeBatchPrefix mdp 1 n :=
    Preorder.frestrictLe n
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionFunctionalResidual feature state action -
      (tilt ^ 2 / 8) * batch.aggregateVisitReal state action
  have hZbatch : Measurable Zbatch :=
    (EpisodeBatch.measurable_aggregateTransitionFunctionalResidual
      feature state action |>.const_mul tilt).sub
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
        policy.iidEpisodeBatchMeasure_one_aggregateTransitionFunctionalResidual_compensated_hasMGFUpperBoundAt
          initialState feature hfeature state action tilt
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
    simpa [Zbatch, aggregateTransitionFunctionalResidualIncrement,
      aggregateTransitionFunctionalResidualPrefix, aggregateVisitIncrement,
      aggregateVisitPrefix, Preorder.frestrictLe_apply] using
      source.integrable_exp_mul_aggregateTransitionFunctionalResidual_compensatedIncrement
        feature hfeature state action (n + 1) tilt (tilt ^ 2 / 8) s
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
  simpa [Zbatch, aggregateTransitionFunctionalResidualIncrement,
    aggregateTransitionFunctionalResidualPrefix, aggregateVisitIncrement,
    aggregateVisitPrefix, Preorder.frestrictLe_apply] using hcomap

theorem aggregateTransitionFunctionalResidual_zero_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (state : State) (action : Action) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        tilt * source.aggregateTransitionFunctionalResidualIncrement
            feature state action 0 trajectory -
          (tilt ^ 2 / 8) * source.aggregateVisitIncrement state action 0 trajectory)
      1 0 source.trajectoryMeasure := by
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.aggregateTransitionFunctionalResidual feature state action -
      (tilt ^ 2 / 8) * batch.aggregateVisitReal state action
  have hbatch : Concentration.HasMGFUpperBoundAt Zbatch 1 0
      (source.initialPolicy.iidEpisodeBatchMeasure initialState 1) := by
    simpa [Zbatch] using
      source.initialPolicy.iidEpisodeBatchMeasure_one_aggregateTransitionFunctionalResidual_compensated_hasMGFUpperBoundAt
        initialState feature hfeature state action tilt
  rw [← source.trajectoryMeasure_map_eval_zero] at hbatch
  have hlift := Concentration.HasMGFUpperBoundAt.of_map
    (X := Zbatch)
    (Z := fun trajectory : EpisodeBatchTrajectory mdp 1 => trajectory 0)
    (measurable_pi_apply 0).aemeasurable hbatch
  simpa [Zbatch, aggregateTransitionFunctionalResidualIncrement,
    aggregateTransitionFunctionalResidualPrefix, aggregateVisitIncrement,
    aggregateVisitPrefix, Preorder.frestrictLe_apply] using hlift

/-- Summing the generated functional-probe increments is exactly the finite
linear combination of the cumulative singleton residuals. -/
theorem sum_aggregateTransitionFunctionalResidualIncrement_eq_prefixResidual
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (trajectory : EpisodeBatchTrajectory mdp 1) (round : Nat)
    (feature : State -> Real) (state : State) (action : Action) :
    (∑ i ∈ Finset.range (round + 1),
        source.aggregateTransitionFunctionalResidualIncrement
          feature state action i trajectory) =
      ∑ nextState : State, feature nextState *
        ((adaptiveCumulativeAggregateTransitionCountAt trajectory round
            state action nextState : Real) -
          (adaptiveCumulativeAggregateVisitCountAt trajectory round
            state action : Real) *
            (mdp.transition (state, action)).real {nextState}) := by
  classical
  simp only [aggregateTransitionFunctionalResidualIncrement,
    aggregateTransitionFunctionalResidualPrefix, Preorder.frestrictLe_apply,
    EpisodeBatch.aggregateTransitionFunctionalResidual]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro nextState _
  rw [← Finset.mul_sum]
  have hcoordinate :=
    source.sum_aggregateTransitionResidualIncrement_eq_prefixAggregateResidual
      trajectory round state action nextState
  simpa [aggregateTransitionResidualIncrement,
    aggregateTransitionResidualPrefix, Preorder.frestrictLe_apply] using
    congrArg (fun value : Real => feature nextState * value) hcoordinate

/-- At positive actual count, the functional residual divided by that count is
exactly `(P_hat-P) feature` for the empirical kernel consumed by the planner. -/
theorem aggregateTransitionFunctionalResidual_eq_count_mul_transitionValue_sub
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (trajectory : EpisodeBatchTrajectory mdp 1) (round : Nat)
    (defaultState : State) (feature : State -> Real)
    (state : State) (action : Action)
    (hpos : 0 < adaptiveCumulativeAggregateVisitCountAt trajectory round
      state action) :
    (∑ i ∈ Finset.range (round + 1),
        source.aggregateTransitionFunctionalResidualIncrement
          feature state action i trajectory) =
      (adaptiveCumulativeAggregateVisitCountAt trajectory round
          state action : Real) *
        ((∫ nextState, feature nextState
            ∂TransitionCountSummary.aggregateEmpiricalTransitionKernel
              (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
              defaultState (state, action)) -
          mdp.transitionValue feature state action) := by
  rw [source.sum_aggregateTransitionFunctionalResidualIncrement_eq_prefixResidual]
  let summary := (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
  have hintegral := summary.integral_aggregateEmpiricalTransitionKernel_eq_sum_div
    defaultState feature state action hpos
  have hcount_ne :
      (adaptiveCumulativeAggregateVisitCountAt trajectory round state action : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have hcount_eq : (adaptiveCumulativeAggregateVisitCountAt trajectory round
      state action : Real) = (summary.aggregateVisitCount state action : Real) := rfl
  rw [hintegral, mdp.transitionValue_eq_sum_measureReal]
  rw [hcount_eq]
  change (∑ nextState : State, feature nextState *
        ((summary.aggregateTransitionCount state action nextState : Real) -
          (summary.aggregateVisitCount state action : Real) *
            (mdp.transition (state, action)).real {nextState})) = _
  rw [mul_sub]
  have hsummary_ne : (summary.aggregateVisitCount state action : Real) ≠ 0 := by
    simpa [hcount_eq] using hcount_ne
  rw [mul_div_cancel₀ _ hsummary_ne]
  have hmul :
      (summary.aggregateVisitCount state action : Real) *
          (∑ nextState : State,
            feature nextState * (mdp.transition (state, action)).real {nextState}) =
        ∑ nextState : State,
          (summary.aggregateVisitCount state action : Real) *
            (feature nextState *
              (mdp.transition (state, action)).real {nextState}) := by
    simpa only using
      (Finset.mul_sum (s := (Finset.univ : Finset State))
        (a := (summary.aggregateVisitCount state action : Real))
        (f := fun nextState : State =>
          feature nextState *
            (mdp.transition (state, action)).real {nextState}))
  rw [hmul]
  change (∑ nextState : State,
      feature nextState *
        ((summary.aggregateTransitionCount state action nextState : Real) -
          (summary.aggregateVisitCount state action : Real) *
            (mdp.transition (state, action)).real {nextState})) =
    (∑ nextState : State,
      feature nextState *
        (summary.aggregateTransitionCount state action nextState : Real)) -
    (∑ nextState : State,
      (summary.aggregateVisitCount state action : Real) *
        (feature nextState *
          (mdp.transition (state, action)).real {nextState}))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro nextState _
  ring

theorem measure_abs_aggregateTransitionFunctionalResidualSum_ge_inter_visitSum_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (feature : State -> Real)
    (hfeature : ∀ nextState, feature nextState ∈ Set.Icc (0 : Real) 1)
    (state : State) (action : Action)
    (rounds : Nat) (tilt threshold visitBudget : Real) (htilt : 0 < tilt) :
    source.trajectoryMeasure
        {trajectory |
          threshold <=
              |∑ i ∈ Finset.range rounds,
                source.aggregateTransitionFunctionalResidualIncrement
                  feature state action i trajectory| ∧
            (∑ i ∈ Finset.range rounds,
                source.aggregateVisitIncrement state action i trajectory) <=
              visitBudget} <=
      2 * ENNReal.ofReal
        (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) := by
  let F := batchPrefixFiltration (mdp := mdp) 1
  let Y : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    source.aggregateTransitionFunctionalResidualIncrement feature state action i trajectory
  let V : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
    source.aggregateVisitIncrement state action i trajectory
  have upper : ∀ sign : Bool,
      source.trajectoryMeasure
        {trajectory |
          threshold <= ∑ i ∈ Finset.range rounds,
            (if sign then Y i trajectory else -Y i trajectory) ∧
          (∑ i ∈ Finset.range rounds, V i trajectory) <= visitBudget} <=
        ENNReal.ofReal
          (Real.exp (-tilt * threshold + (tilt ^ 2 / 8) * visitBudget)) := by
    intro sign
    let signedTilt := if sign then tilt else -tilt
    let Ysign : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      if sign then Y i trajectory else -Y i trajectory
    let Z : Nat -> EpisodeBatchTrajectory mdp 1 -> Real := fun i trajectory =>
      tilt * Ysign i trajectory - (tilt ^ 2 / 8) * V i trajectory
    have hadapted : StronglyAdapted F Z := by
      have h := source.aggregateTransitionFunctionalResidual_compensated_stronglyAdapted_piLE
        feature state action signedTilt (signedTilt ^ 2 / 8)
      cases sign <;> simpa [F, Y, V, Ysign, Z, signedTilt] using h
    have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 0
        source.trajectoryMeasure := by
      have h := source.aggregateTransitionFunctionalResidual_zero_compensated_hasMGFUpperBoundAt
        feature hfeature state action signedTilt
      cases sign <;> simpa [Y, V, Ysign, Z, signedTilt] using h
    have hsucc : ∀ i, i < rounds - 1 ->
        Concentration.HasCondMGFUpperBoundAt
          (F i) (F.le i) (Z (i + 1)) 1 0 source.trajectoryMeasure := by
      intro i _hi
      have h := source.aggregateTransitionFunctionalResidual_succ_compensated_hasCondMGFUpperBoundAt
        feature hfeature state action i signedTilt
      cases sign <;> simpa [F, Y, V, Ysign, Z, signedTilt] using h
    simpa [Y, V, Ysign] using
      (Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
        (μ := source.trajectoryMeasure) (ℱ := F) Ysign V rounds tilt
        (tilt ^ 2 / 8) threshold visitBudget hadapted hzero hsucc htilt.le
        (by positivity))
  let positive : Set (EpisodeBatchTrajectory mdp 1) :=
    {trajectory | threshold <= ∑ i ∈ Finset.range rounds, Y i trajectory ∧
      (∑ i ∈ Finset.range rounds, V i trajectory) <= visitBudget}
  let negative : Set (EpisodeBatchTrajectory mdp 1) :=
    {trajectory | threshold <= ∑ i ∈ Finset.range rounds, -Y i trajectory ∧
      (∑ i ∈ Finset.range rounds, V i trajectory) <= visitBudget}
  have hsubset :
      {trajectory |
          threshold <= |∑ i ∈ Finset.range rounds, Y i trajectory| ∧
          (∑ i ∈ Finset.range rounds, V i trajectory) <= visitBudget} ⊆
        positive ∪ negative := by
    intro trajectory htrajectory
    rcases htrajectory with ⟨habs, hvis⟩
    rw [le_abs] at habs
    rcases habs with hpos | hneg
    · exact Set.mem_union_left _ ⟨hpos, hvis⟩
    · refine Set.mem_union_right _ ⟨?_, hvis⟩
      simpa [Finset.sum_neg_distrib] using hneg
  calc
    source.trajectoryMeasure _ <= source.trajectoryMeasure (positive ∪ negative) :=
      measure_mono (by simpa [Y, V] using hsubset)
    _ <= source.trajectoryMeasure positive + source.trajectoryMeasure negative :=
      measure_union_le _ _
    _ <= ENNReal.ofReal (Real.exp (-tilt * threshold +
          (tilt ^ 2 / 8) * visitBudget)) +
        ENNReal.ofReal (Real.exp (-tilt * threshold +
          (tilt ^ 2 / 8) * visitBudget)) := by
      exact add_le_add
        (by simpa [positive, Y, V] using upper true)
        (by simpa [negative, Y, V] using upper false)
    _ = 2 * ENNReal.ofReal (Real.exp (-tilt * threshold +
          (tilt ^ 2 / 8) * visitBudget)) := by ring

end AdaptiveEpisodeBatchSource

end BanditRLProof.FiniteHorizonRL
