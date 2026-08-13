import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVILocalBellman

/-!
# Stage-resolved Bellman innovation for UCBVI-CH

This file proves the within-episode martingale bound for an arbitrary fixed
chronological table of continuation gaps in `[0,H]`.  The proof recurses
through the actual policy trajectory kernel one transition at a time, so its
variance budget is `H * H^2 / 4`, rather than the invalid whole-episode
range-square budget `H^4 / 4`.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MDP

/-- Chronological Bellman innovation for a deterministic action table.  The
sampled action coordinate is deliberately ignored: the table chooses the
action from the recursively reconstructed current state.  This makes the
pathwise recursion canonical on every batch, while its law is still the exact
generated deterministic-policy trajectory law. -/
noncomputable def sampledCumulativeDeterministicGapInnovationFrom
    (mdp : MDP State Action) (table : DeterministicMarkovPolicyTable mdp)
    (feature : Fin mdp.horizon -> State -> Real) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State ->
      StepTrace Action State remaining -> Real
  | 0, _, _, _ => 0
  | remaining + 1, hremaining, state, trace =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      mdp.transitionValue (feature stage) state (table stage state) -
          feature stage (trace 0).2 +
        sampledCumulativeDeterministicGapInnovationFrom mdp table feature
          remaining (by omega) (trace 0).2 (Fin.tail trace)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_sampledCumulativeDeterministicGapInnovationFrom
    (mdp : MDP State Action) (table : DeterministicMarkovPolicyTable mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    Measurable (fun p : State × StepTrace Action State remaining =>
      mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
        remaining hremaining p.1 p.2) := by
  induction remaining with
  | zero => simp [sampledCumulativeDeterministicGapInnovationFrom]
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let head : State × StepTrace Action State (remaining + 1) ->
          Action × State := fun p => p.2 0
      have hhead : Measurable head :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : State × StepTrace Action State (remaining + 1) =>
            ((head p).2, Fin.tail p.2)) :=
        (hhead.snd.prodMk
          ((StepTrace.measurable_tail remaining).comp measurable_snd))
      have hcurrent : Measurable
          (fun p : State × StepTrace Action State (remaining + 1) =>
            mdp.transitionValue (feature stage) p.1 (table stage p.1) -
              feature stage (p.2 0).2) := measurable_of_finite _
      simpa only [sampledCumulativeDeterministicGapInnovationFrom] using
        hcurrent.add ((ih (by omega)).comp htail)

omit [Nonempty State] [Nonempty Action] in
theorem actionStateKernel_deterministicGapInnovation_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (table : DeterministicMarkovPolicyTable mdp)
    (feature : State -> Real)
    (hfeature : forall nextState,
      feature nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (stage : Fin mdp.horizon) (currentState : State) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun head : Action × State =>
        tilt * (mdp.transitionValue feature currentState (table stage currentState) -
          feature head.2) - tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      1 0 (table.toMarkovPolicy.actionStateKernel stage currentState) := by
  let selected := table stage currentState
  let Z : Action × State -> Real := fun head =>
    tilt * (mdp.transitionValue feature currentState selected - feature head.2) -
      tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  have hmean : (∫ nextState, feature nextState
      ∂mdp.transition (currentState, selected)) =
      mdp.transitionValue feature currentState selected := rfl
  have hsub := Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
    (mdp.transition (currentState, selected))
    (measurable_of_finite feature).aemeasurable
    (Filter.Eventually.of_forall hfeature) hmean
  have hneg : ProbabilityTheory.HasSubgaussianMGF
      (fun nextState => mdp.transitionValue feature currentState selected -
        feature nextState)
      (Concentration.intervalVarianceProxy 0 (mdp.horizon : Real))
      (mdp.transition (currentState, selected)) := by
    convert hsub.neg using 1
    funext nextState
    simp
  have hproxy : (((Concentration.intervalVarianceProxy 0
      (mdp.horizon : Real) : NNReal) : Real)) =
      (mdp.horizon : Real) ^ 2 / 4 := by
    simp [Concentration.intervalVarianceProxy]
    ring
  have hmgf := hneg.mgf_le tilt
  rw [hproxy] at hmgf
  have hfixed : Concentration.HasMGFUpperBoundAt
      (fun nextState => mdp.transitionValue feature currentState selected -
        feature nextState) tilt
      (tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      (mdp.transition (currentState, selected)) := by
    constructor
    · exact hneg.integrable_exp_mul
    · convert hmgf using 1 <;> ring
  have hcomp := hfixed.compensated
  constructor
  · intro s
    exact integrable_of_fintype _ _ (by fun_prop)
  · rw [ProbabilityTheory.mgf]
    change (∫ head, Real.exp (1 * Z head)
      ∂table.toMarkovPolicy.actionStateKernel stage currentState) <= Real.exp 0
    unfold MarkovPolicy.actionStateKernel
    have hint : Integrable (fun head => Real.exp (1 * Z head))
        (((table.toMarkovPolicy.actionKernel stage).compProd mdp.transition)
          currentState) := integrable_of_fintype _ _ (by fun_prop)
    rw [ProbabilityTheory.integral_compProd hint]
    unfold DeterministicMarkovPolicyTable.toMarkovPolicy
    rw [ProbabilityTheory.Kernel.deterministic_apply]
    rw [integral_dirac']
    · simpa [ProbabilityTheory.mgf, Z, selected] using hcomp.mgf_le
    · exact measurable_of_finite _ |>.stronglyMeasurable

omit [Nonempty State] [Nonempty Action] in
/-- Stage-resolved MGF for the canonicalized deterministic trajectory. -/
theorem trajectoryKernelRemaining_deterministicGapInnovation_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (table : DeterministicMarkovPolicyTable mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (tilt : Real) (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (currentState : State) :
    Concentration.HasMGFUpperBoundAt
      (fun trace =>
        tilt * mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
            remaining hremaining currentState trace -
          (remaining : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      1 0 (table.toMarkovPolicy.trajectoryKernelRemaining remaining hremaining
        currentState) := by
  induction remaining generalizing currentState with
  | zero =>
      have hzero : Concentration.HasMGFUpperBoundAt
          (fun _trace : StepTrace Action State 0 => (0 : Real)) 1 0
          (table.toMarkovPolicy.trajectoryKernelRemaining 0 hremaining currentState) := by
        constructor
        · intro s
          exact integrable_of_fintype _ _ (by fun_prop)
        · simp [ProbabilityTheory.mgf]
      simpa [sampledCumulativeDeterministicGapInnovationFrom] using hzero
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let policy := table.toMarkovPolicy
      let tailKernel : ProbabilityTheory.Kernel
          (State × (Action × State)) (StepTrace Action State remaining) :=
        (policy.trajectoryKernelRemaining remaining (by omega)).comap
          (fun p : State × (Action × State) => p.2.2) measurable_snd.snd
      let consStep := fun p : (Action × State) × StepTrace Action State remaining =>
        @Fin.cons remaining (fun _ => Action × State) p.1 p.2
      let Z : StepTrace Action State (remaining + 1) -> Real := fun trace =>
        tilt * mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
            (remaining + 1) hremaining currentState trace -
          ((remaining + 1 : Nat) : Real) * tilt ^ 2 *
            (mdp.horizon : Real) ^ 2 / 8
      let Zhead : Action × State -> Real := fun head =>
        tilt * (mdp.transitionValue (feature stage) currentState
          (table stage currentState) - feature stage head.2) -
        tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
      let Ztail : (Action × State) × StepTrace Action State remaining -> Real :=
        fun p => tilt * mdp.sampledCumulativeDeterministicGapInnovationFrom
            table feature remaining (by omega) p.1.2 p.2 -
          (remaining : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
      have hcons : Measurable consStep := StepTrace.measurable_cons remaining
      have hZ : Measurable Z :=
        ((mdp.measurable_sampledCumulativeDeterministicGapInnovationFrom table
          feature (remaining + 1) hremaining).comp
            (measurable_const.prodMk measurable_id)).const_mul tilt |>.sub
          measurable_const
      have hpair : Integrable (fun p => Real.exp (1 * Z (consStep p)))
          (((policy.actionStateKernel stage).compProd tailKernel) currentState) :=
        integrable_of_fintype _ _ (Real.measurable_exp.comp
          ((hZ.comp hcons).const_mul 1))
      have hhead := mdp.actionStateKernel_deterministicGapInnovation_compensated_hasMGFUpperBoundAt
        table (feature stage) (hfeature stage) stage currentState tilt
      have htail : forall head : Action × State,
          Concentration.HasMGFUpperBoundAt (fun tail => Ztail (head, tail)) 1 0
            (policy.trajectoryKernelRemaining remaining (by omega) head.2) := by
        intro head
        simpa [Ztail, policy] using ih (by omega) head.2
      constructor
      · intro s
        exact integrable_of_fintype _ _ (by fun_prop)
      · rw [ProbabilityTheory.mgf]
        change (∫ trace, Real.exp (1 * Z trace)
          ∂policy.trajectoryKernelRemaining (remaining + 1) hremaining
            currentState) <= Real.exp 0
        rw [MarkovPolicy.trajectoryKernelRemaining]
        rw [ProbabilityTheory.Kernel.map_apply _ hcons]
        change (∫ trace, (fun trace => Real.exp (1 * Z trace)) trace
          ∂Measure.map consStep
            (((policy.actionStateKernel stage).compProd tailKernel)
              currentState)) <= Real.exp 0
        have hfm : AEStronglyMeasurable (fun trace => Real.exp (1 * Z trace))
            (Measure.map consStep
              (((policy.actionStateKernel stage).compProd tailKernel)
                currentState)) :=
          (Real.measurable_exp.comp (hZ.const_mul 1)).aestronglyMeasurable
        rw [integral_map hcons.aemeasurable hfm]
        rw [ProbabilityTheory.integral_compProd hpair]
        simp only [Real.exp_zero]
        have hinner : forall head : Action × State,
            (∫ tail, Real.exp (1 * Z (consStep (head, tail)))
              ∂tailKernel (currentState, head)) <= Real.exp (Zhead head) := by
          intro head
          change (∫ tail, Real.exp (1 * Z (consStep (head, tail)))
            ∂policy.trajectoryKernelRemaining remaining (by omega) head.2) <= _
          have hz : forall tail,
              Z (consStep (head, tail)) = Zhead head + Ztail (head, tail) := by
            intro tail
            simp only [Z, Zhead, Ztail, consStep,
              sampledCumulativeDeterministicGapInnovationFrom]
            simp [stage]
            push_cast
            ring
          simp_rw [hz, mul_add, Real.exp_add, one_mul, integral_const_mul]
          have htailMgf : (∫ tail, Real.exp (Ztail (head, tail))
              ∂policy.trajectoryKernelRemaining remaining (by omega) head.2) <= 1 := by
            simpa [ProbabilityTheory.mgf] using (htail head).mgf_le
          simpa using mul_le_mul_of_nonneg_left htailMgf
            (Real.exp_pos (Zhead head)).le
        have hleft : Integrable (fun head =>
            ∫ tail, Real.exp (1 * Z (consStep (head, tail)))
              ∂tailKernel (currentState, head))
            (policy.actionStateKernel stage currentState) :=
          integrable_of_fintype _ _ (measurable_of_finite _)
        have hright : Integrable (fun head => Real.exp (Zhead head))
            (policy.actionStateKernel stage currentState) :=
          integrable_of_fintype _ _ (measurable_of_finite _)
        calc
          (∫ head, ∫ tail, Real.exp (1 * Z (consStep (head, tail)))
              ∂tailKernel (currentState, head)
              ∂policy.actionStateKernel stage currentState) <=
              ∫ head, Real.exp (Zhead head)
                ∂policy.actionStateKernel stage currentState :=
            integral_mono_ae hleft hright (Filter.Eventually.of_forall hinner)
          _ <= 1 := by
            simpa [ProbabilityTheory.mgf, Zhead, policy] using hhead.mgf_le

omit [Nonempty State] [Nonempty Action] in
/-- Integrating the start state preserves the canonical deterministic-table
stage-resolved MGF. -/
theorem trajectoryMeasure_deterministicGapInnovation_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory =>
        tilt * mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
            mdp.horizon le_rfl trajectory.1 trajectory.2 -
          (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      1 0 (table.toMarkovPolicy.trajectoryMeasure initialState) := by
  let policy := table.toMarkovPolicy
  let Z : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
        mdp.horizon le_rfl trajectory.1 trajectory.2 -
      (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  have hZ : Measurable Z :=
    (mdp.measurable_sampledCumulativeDeterministicGapInnovationFrom table feature
      mdp.horizon le_rfl |>.const_mul tilt).sub measurable_const
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
    have hfiber : forall state : State,
        (∫ trace, Real.exp (1 * Z (state, trace))
          ∂policy.trajectoryKernelRemaining mdp.horizon le_rfl state) <= 1 := by
      intro state
      have h :=
        mdp.trajectoryKernelRemaining_deterministicGapInnovation_compensated_hasMGFUpperBoundAt
          table feature hfeature tilt mdp.horizon le_rfl state
      simpa [ProbabilityTheory.mgf, Z, policy] using h.mgf_le
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
/-- Pathwise envelope for the canonical deterministic-table innovation. -/
theorem abs_sampledCumulativeDeterministicGapInnovationFrom_le
    (mdp : MDP State Action) (table : DeterministicMarkovPolicyTable mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon) :
    forall remaining (hremaining : remaining <= mdp.horizon)
      (currentState : State) (trace : StepTrace Action State remaining),
      |mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
        remaining hremaining currentState trace| <=
        (remaining : Real) * mdp.horizon := by
  intro remaining
  induction remaining with
  | zero => simp [sampledCumulativeDeterministicGapInnovationFrom]
  | succ remaining ih =>
      intro hremaining currentState trace
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let selected := table stage currentState
      have hintegrable : Integrable (feature stage)
          (mdp.transition (currentState, selected)) :=
        integrable_of_fintype _ _ (measurable_of_finite _)
      have htransitionLower :
          0 <= mdp.transitionValue (feature stage) currentState selected := by
        unfold transitionValue
        exact integral_nonneg fun nextState => (hfeature stage nextState).1
      have htransitionUpper :
          mdp.transitionValue (feature stage) currentState selected <=
            (mdp.horizon : Real) := by
        unfold transitionValue
        calc
          (∫ nextState, feature stage nextState
            ∂mdp.transition (currentState, selected)) <=
              ∫ _nextState, (mdp.horizon : Real)
                ∂mdp.transition (currentState, selected) :=
            integral_mono hintegrable (integrable_const _) fun nextState =>
              (hfeature stage nextState).2
          _ = (mdp.horizon : Real) := by simp
      have hhead :
          |mdp.transitionValue (feature stage) currentState selected -
              feature stage (trace 0).2| <= (mdp.horizon : Real) := by
        rw [abs_le]
        constructor <;> linarith [hfeature stage (trace 0).2 |>.1,
          hfeature stage (trace 0).2 |>.2]
      have htail := ih (by omega) (trace 0).2 (Fin.tail trace)
      rw [sampledCumulativeDeterministicGapInnovationFrom]
      calc
        |_ + _| <=
            |mdp.transitionValue (feature stage) currentState selected -
              feature stage (trace 0).2| +
            |mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
              remaining (by omega) (trace 0).2 (Fin.tail trace)| := abs_add_le _ _
        _ <= (mdp.horizon : Real) +
            (remaining : Real) * mdp.horizon := add_le_add hhead htail
        _ = ((remaining + 1 : Nat) : Real) * mdp.horizon := by
          push_cast
          ring

/-- Sum of chronological transition innovations for a stage-indexed bounded
continuation table. -/
noncomputable def sampledCumulativeTransitionGapInnovationFrom
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (feature : Fin mdp.horizon -> State -> Real) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State ->
      StepTrace Action State remaining -> Real
  | 0, _, _, _ => 0
  | remaining + 1, hremaining, state, trace =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      mdp.transitionValue (feature stage) state (trace 0).1 -
          feature stage (trace 0).2 +
        sampledCumulativeTransitionGapInnovationFrom mdp policy feature
          remaining (by omega) (trace 0).2 (Fin.tail trace)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_sampledCumulativeTransitionGapInnovationFrom
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    Measurable (fun p : State × StepTrace Action State remaining =>
      mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
        remaining hremaining p.1 p.2) := by
  induction remaining with
  | zero =>
      simp [sampledCumulativeTransitionGapInnovationFrom]
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let head : State × StepTrace Action State (remaining + 1) ->
          Action × State := fun p => p.2 0
      have hhead : Measurable head := (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : State × StepTrace Action State (remaining + 1) =>
            ((head p).2, Fin.tail p.2)) :=
        hhead.snd.prodMk
          ((StepTrace.measurable_tail remaining).comp measurable_snd)
      have hcurrent : Measurable
          (fun p : State × StepTrace Action State (remaining + 1) =>
            mdp.transitionValue (feature stage) p.1 (head p).1 -
              feature stage (head p).2) := by
        exact measurable_of_finite _
      simpa only [sampledCumulativeTransitionGapInnovationFrom] using
        hcurrent.add ((ih (by omega)).comp htail)

omit [Nonempty State] [Nonempty Action] in
/-- Pathwise envelope matching the sum of `remaining` centered `[0,H]`
transition probes. -/
theorem abs_sampledCumulativeTransitionGapInnovationFrom_le
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon) :
    forall remaining (hremaining : remaining <= mdp.horizon)
      (currentState : State) (trace : StepTrace Action State remaining),
      |mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
        remaining hremaining currentState trace| <=
        (remaining : Real) * mdp.horizon := by
  intro remaining
  induction remaining with
  | zero => simp [sampledCumulativeTransitionGapInnovationFrom]
  | succ remaining ih =>
      intro hremaining currentState trace
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let chosenAction := (trace 0).1
      have hintegrable : Integrable (feature stage)
          (mdp.transition (currentState, chosenAction)) :=
        integrable_of_fintype _ _ (measurable_of_finite _)
      have htransitionLower :
          0 <= mdp.transitionValue (feature stage) currentState chosenAction := by
        unfold transitionValue
        exact integral_nonneg fun nextState => (hfeature stage nextState).1
      have htransitionUpper :
          mdp.transitionValue (feature stage) currentState chosenAction <=
            (mdp.horizon : Real) := by
        unfold transitionValue
        calc
          (∫ nextState, feature stage nextState
            ∂mdp.transition (currentState, chosenAction)) <=
              ∫ _nextState, (mdp.horizon : Real)
                ∂mdp.transition (currentState, chosenAction) :=
            integral_mono hintegrable (integrable_const _) fun nextState =>
              (hfeature stage nextState).2
          _ = (mdp.horizon : Real) := by simp
      have hhead :
          |mdp.transitionValue (feature stage) currentState chosenAction -
              feature stage (trace 0).2| <= (mdp.horizon : Real) := by
        rw [abs_le]
        constructor <;> linarith [hfeature stage (trace 0).2 |>.1,
          hfeature stage (trace 0).2 |>.2]
      have htail := ih (by omega) (trace 0).2 (Fin.tail trace)
      rw [sampledCumulativeTransitionGapInnovationFrom]
      calc
        |_ + _| <=
            |mdp.transitionValue (feature stage) currentState chosenAction -
              feature stage (trace 0).2| +
            |mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
              remaining (by omega) (trace 0).2 (Fin.tail trace)| := abs_add_le _ _
        _ <= (mdp.horizon : Real) +
            (remaining : Real) * mdp.horizon := add_le_add hhead htail
        _ = ((remaining + 1 : Nat) : Real) * mdp.horizon := by
          push_cast
          ring

omit [Nonempty State] [Nonempty Action] in
/-- One policy transition has the Hoeffding compensated MGF with range `H`. -/
theorem actionStateKernel_transitionGapInnovation_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (feature : State -> Real)
    (hfeature : forall nextState,
      feature nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (stage : Fin mdp.horizon) (currentState : State) (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun head : Action × State =>
        tilt * (mdp.transitionValue feature currentState head.1 -
          feature head.2) -
        tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      1 0 (policy.actionStateKernel stage currentState) := by
  let Z : Action × State -> Real := fun head =>
    tilt * (mdp.transitionValue feature currentState head.1 -
      feature head.2) - tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  constructor
  · intro s
    exact integrable_of_fintype _ _ (by fun_prop)
  · rw [ProbabilityTheory.mgf]
    change (∫ head, Real.exp (1 * Z head)
      ∂policy.actionStateKernel stage currentState) <= Real.exp 0
    unfold MarkovPolicy.actionStateKernel
    have hint : Integrable (fun head => Real.exp (1 * Z head))
        ((policy.actionKernel stage).compProd mdp.transition currentState) :=
      integrable_of_fintype _ _ (by fun_prop)
    rw [ProbabilityTheory.integral_compProd hint]
    simp only [Real.exp_zero]
    have hinner : forall chosenAction : Action,
        (∫ nextState,
          Real.exp (Z (chosenAction, nextState))
            ∂mdp.transition (currentState, chosenAction)) <= 1 := by
      intro chosenAction
      have hmean :
          (∫ nextState, feature nextState
            ∂mdp.transition (currentState, chosenAction)) =
          mdp.transitionValue feature currentState chosenAction := rfl
      have hsub :=
        Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
          (mdp.transition (currentState, chosenAction))
          (measurable_of_finite feature).aemeasurable
          (Filter.Eventually.of_forall hfeature) hmean
      have hneg : ProbabilityTheory.HasSubgaussianMGF
          (fun nextState =>
            mdp.transitionValue feature currentState chosenAction -
              feature nextState)
          (Concentration.intervalVarianceProxy 0 (mdp.horizon : Real))
          (mdp.transition (currentState, chosenAction)) := by
        convert hsub.neg using 1
        funext nextState
        simp
      have hproxy :
          (((Concentration.intervalVarianceProxy 0 (mdp.horizon : Real) :
              NNReal) : Real)) = (mdp.horizon : Real) ^ 2 / 4 := by
        simp [Concentration.intervalVarianceProxy]
        ring
      have hmgf := hneg.mgf_le tilt
      rw [hproxy] at hmgf
      have hfixed : Concentration.HasMGFUpperBoundAt
          (fun nextState =>
            mdp.transitionValue feature currentState chosenAction -
              feature nextState)
          tilt (tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
          (mdp.transition (currentState, chosenAction)) := by
        constructor
        · exact hneg.integrable_exp_mul
        · convert hmgf using 1 <;> ring
      have hcomp := hfixed.compensated
      simpa [ProbabilityTheory.mgf, Z] using hcomp.mgf_le
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
/-- Recursive within-episode MGF.  Each of the `remaining` transitions pays
exactly one `tilt^2 H^2 / 8` compensation. -/
theorem trajectoryKernelRemaining_transitionGapInnovation_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (tilt : Real) (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (currentState : State) :
    Concentration.HasMGFUpperBoundAt
      (fun trace =>
        tilt * mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
            remaining hremaining currentState trace -
          (remaining : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
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
      simpa [sampledCumulativeTransitionGapInnovationFrom] using hzero
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
        tilt * mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
            (remaining + 1) hremaining currentState trace -
          ((remaining + 1 : Nat) : Real) * tilt ^ 2 *
            (mdp.horizon : Real) ^ 2 / 8
      let Zhead : Action × State -> Real := fun head =>
        tilt * (mdp.transitionValue (feature stage) currentState head.1 -
          feature stage head.2) -
        tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
      let Ztail : (Action × State) × StepTrace Action State remaining -> Real :=
        fun p =>
          tilt * mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
              remaining (by omega) p.1.2 p.2 -
            (remaining : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
      have hcons : Measurable consStep := StepTrace.measurable_cons remaining
      have hZ : Measurable Z :=
        ((mdp.measurable_sampledCumulativeTransitionGapInnovationFrom policy
          feature (remaining + 1) hremaining).comp
            (measurable_const.prodMk measurable_id)).const_mul tilt |>.sub
          measurable_const
      have hpair : Integrable (fun p => Real.exp (1 * Z (consStep p)))
          (((policy.actionStateKernel stage).compProd tailKernel) currentState) :=
        integrable_of_fintype _ _ (Real.measurable_exp.comp
          ((hZ.comp hcons).const_mul 1))
      have hhead :=
        mdp.actionStateKernel_transitionGapInnovation_compensated_hasMGFUpperBoundAt
          policy (feature stage) (hfeature stage) stage currentState tilt
      have htail : forall head : Action × State,
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
          ∂policy.trajectoryKernelRemaining (remaining + 1) hremaining
            currentState) <= Real.exp 0
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
        have hinner : forall head : Action × State,
            (∫ tail, Real.exp (1 * Z (consStep (head, tail)))
              ∂tailKernel (currentState, head)) <= Real.exp (Zhead head) := by
          intro head
          have htailApply : tailKernel (currentState, head) =
              policy.trajectoryKernelRemaining remaining (by omega) head.2 := by
            rfl
          rw [htailApply]
          have hz : forall tail,
              Z (consStep (head, tail)) = Zhead head + Ztail (head, tail) := by
            intro tail
            simp only [Z, Zhead, Ztail, consStep,
              sampledCumulativeTransitionGapInnovationFrom]
            simp [stage]
            push_cast
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
/-- Integrating the start state preserves the exact stage-resolved MGF. -/
theorem trajectoryMeasure_transitionGapInnovation_compensated_hasMGFUpperBoundAt
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory =>
        tilt * mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
            mdp.horizon le_rfl trajectory.1 trajectory.2 -
          (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      1 0 (policy.trajectoryMeasure initialState) := by
  let Z : State × StepTrace Action State mdp.horizon -> Real := fun trajectory =>
    tilt * mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
        mdp.horizon le_rfl trajectory.1 trajectory.2 -
      (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  have hZ : Measurable Z :=
    (mdp.measurable_sampledCumulativeTransitionGapInnovationFrom policy feature
      mdp.horizon le_rfl |>.const_mul tilt).sub measurable_const
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
    have hfiber : forall state : State,
        (∫ trace, Real.exp (1 * Z (state, trace))
          ∂policy.trajectoryKernelRemaining mdp.horizon le_rfl state) <= 1 := by
      intro state
      have h :=
        mdp.trajectoryKernelRemaining_transitionGapInnovation_compensated_hasMGFUpperBoundAt
          policy feature hfeature tilt mdp.horizon le_rfl state
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

/-- Initial state reconstructed from the first record of a one-episode batch.
The default branch specifies the degenerate zero-horizon input only. -/
def reconstructedInitialState
    {mdp : MDP State Action} (defaultState : State)
    (batch : EpisodeBatch mdp 1) : State :=
  if hhorizon : 0 < mdp.horizon then (batch 0 ⟨0, hhorizon⟩).state
  else defaultState

/-- Action/next-state trace reconstructed from the one-episode records. -/
def reconstructedStepTrace
    {mdp : MDP State Action} (batch : EpisodeBatch mdp 1) :
    StepTrace Action State mdp.horizon :=
  fun stage => ((batch 0 stage).action, (batch 0 stage).nextState)

omit [Nonempty State] [Nonempty Action] in
theorem measurable_reconstructedInitialState
    {mdp : MDP State Action} (defaultState : State) :
    Measurable (reconstructedInitialState (mdp := mdp) defaultState) := by
  unfold reconstructedInitialState
  split_ifs
  · exact EpisodeStep.measurable_state.comp
      (measurable_pi_apply _ |>.comp (measurable_pi_apply _))
  · exact measurable_const

omit [Nonempty State] [Nonempty Action] in
theorem measurable_reconstructedStepTrace
    {mdp : MDP State Action} :
    Measurable (reconstructedStepTrace (mdp := mdp)) := by
  refine measurable_pi_lambda _ fun stage => ?_
  exact
    (EpisodeStep.measurable_action.comp
      (measurable_pi_apply stage |>.comp (measurable_pi_apply 0))).prodMk
    (EpisodeStep.measurable_nextState.comp
      (measurable_pi_apply stage |>.comp (measurable_pi_apply 0)))

/-- Canonical deterministic-table Bellman innovation read from one generated
batch.  Recorded action fields are intentionally not used. -/
noncomputable def cumulativeDeterministicGapInnovation
    {mdp : MDP State Action} (defaultState : State)
    (table : DeterministicMarkovPolicyTable mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (batch : EpisodeBatch mdp 1) : Real :=
  mdp.sampledCumulativeDeterministicGapInnovationFrom table feature mdp.horizon
    le_rfl (batch.reconstructedInitialState defaultState)
    batch.reconstructedStepTrace

omit [Nonempty State] [Nonempty Action] in
theorem measurable_cumulativeDeterministicGapInnovation
    {mdp : MDP State Action} (defaultState : State)
    (table : DeterministicMarkovPolicyTable mdp)
    (feature : Fin mdp.horizon -> State -> Real) :
    Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.cumulativeDeterministicGapInnovation defaultState table feature) := by
  exact
    (mdp.measurable_sampledCumulativeDeterministicGapInnovationFrom table feature
      mdp.horizon le_rfl).comp
      ((measurable_reconstructedInitialState defaultState).prodMk
        measurable_reconstructedStepTrace)

omit [Nonempty State] [Nonempty Action] in
theorem cumulativeDeterministicGapInnovation_episodeBatchOfTrajectories
    (mdp : MDP State Action) (defaultState : State)
    (table : DeterministicMarkovPolicyTable mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (hhorizon : 0 < mdp.horizon)
    (trajectories : Fin 1 -> State × StepTrace Action State mdp.horizon) :
    EpisodeBatch.cumulativeDeterministicGapInnovation defaultState table feature
        (mdp.episodeBatchOfTrajectories 1 trajectories) =
      mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
        mdp.horizon le_rfl (trajectories 0).1 (trajectories 0).2 := by
  have hinitial :
      EpisodeBatch.reconstructedInitialState defaultState
          (mdp.episodeBatchOfTrajectories 1 trajectories) =
        (trajectories 0).1 := by
    simp [reconstructedInitialState, hhorizon, MDP.episodeBatchOfTrajectories,
      MDP.episodeStepOfTrajectory, MDP.trajectoryStateAt]
  have htrace :
      EpisodeBatch.reconstructedStepTrace
          (mdp.episodeBatchOfTrajectories 1 trajectories) =
        (trajectories 0).2 := by
    funext stage
    simp [reconstructedStepTrace, MDP.episodeBatchOfTrajectories,
      MDP.episodeStepOfTrajectory]
  simp [cumulativeDeterministicGapInnovation, hinitial, htrace]

/-- Stage-resolved Bellman innovation read from one generated batch. -/
noncomputable def cumulativeTransitionGapInnovation
    {mdp : MDP State Action} (defaultState : State)
    (policy : MarkovPolicy mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (batch : EpisodeBatch mdp 1) : Real :=
  mdp.sampledCumulativeTransitionGapInnovationFrom policy feature mdp.horizon
    le_rfl (batch.reconstructedInitialState defaultState)
    batch.reconstructedStepTrace

omit [Nonempty State] [Nonempty Action] in
theorem measurable_cumulativeTransitionGapInnovation
    {mdp : MDP State Action} (defaultState : State)
    (policy : MarkovPolicy mdp)
    (feature : Fin mdp.horizon -> State -> Real) :
    Measurable (fun batch : EpisodeBatch mdp 1 =>
      batch.cumulativeTransitionGapInnovation defaultState policy feature) := by
  exact
    (mdp.measurable_sampledCumulativeTransitionGapInnovationFrom policy feature
      mdp.horizon le_rfl).comp
      ((measurable_reconstructedInitialState defaultState).prodMk
        measurable_reconstructedStepTrace)

omit [Nonempty State] [Nonempty Action] in
/-- Reconstruction is literal on the batch map used by the generated law. -/
theorem cumulativeTransitionGapInnovation_episodeBatchOfTrajectories
    (mdp : MDP State Action) (defaultState : State)
    (policy : MarkovPolicy mdp)
    (feature : Fin mdp.horizon -> State -> Real)
    (hhorizon : 0 < mdp.horizon)
    (trajectories : Fin 1 -> State × StepTrace Action State mdp.horizon) :
    EpisodeBatch.cumulativeTransitionGapInnovation defaultState policy feature
        (mdp.episodeBatchOfTrajectories 1 trajectories) =
      mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
        mdp.horizon le_rfl (trajectories 0).1 (trajectories 0).2 := by
  have hinitial :
      EpisodeBatch.reconstructedInitialState defaultState
          (mdp.episodeBatchOfTrajectories 1 trajectories) =
        (trajectories 0).1 := by
    simp [reconstructedInitialState, hhorizon, MDP.episodeBatchOfTrajectories,
      MDP.episodeStepOfTrajectory, MDP.trajectoryStateAt]
  have htrace :
      EpisodeBatch.reconstructedStepTrace
          (mdp.episodeBatchOfTrajectories 1 trajectories) =
        (trajectories 0).2 := by
    funext stage
    simp [reconstructedStepTrace, MDP.episodeBatchOfTrajectories,
      MDP.episodeStepOfTrajectory]
  simp [cumulativeTransitionGapInnovation, hinitial, htrace]

end EpisodeBatch

namespace DeterministicMarkovPolicyTable

omit [Nonempty State] [Nonempty Action] in
/-- The exact one-episode batch image retains the canonical deterministic-table
stage-resolved MGF. -/
theorem iidEpisodeBatchMeasure_one_cumulativeDeterministicGapInnovation_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (defaultState : State) (hhorizon : 0 < mdp.horizon)
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun batch : EpisodeBatch mdp 1 =>
        tilt * batch.cumulativeDeterministicGapInnovation defaultState table feature -
          (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      1 0 (table.toMarkovPolicy.iidEpisodeBatchMeasure initialState 1) := by
  let policy := table.toMarkovPolicy
  let Ztrace : State × StepTrace Action State mdp.horizon -> Real :=
    fun trajectory =>
      tilt * mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
          mdp.horizon le_rfl trajectory.1 trajectory.2 -
        (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.cumulativeDeterministicGapInnovation defaultState table feature -
      (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  let eval0 : (Fin 1 -> State × StepTrace Action State mdp.horizon) ->
      State × StepTrace Action State mdp.horizon := Function.eval 0
  let batchMap := mdp.episodeBatchOfTrajectories 1
  have htrace :=
    mdp.trajectoryMeasure_deterministicGapInnovation_compensated_hasMGFUpperBoundAt
      table initialState feature hfeature tilt
  have hfamilyMap : Concentration.HasMGFUpperBoundAt Ztrace 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map eval0) := by
    rw [policy.iidTrajectoryFamilyMeasure_map_eval initialState (0 : Fin 1)]
    exact htrace
  have hfamily : Concentration.HasMGFUpperBoundAt (Ztrace ∘ eval0) 1 0
      (policy.iidTrajectoryFamilyMeasure initialState 1) :=
    Concentration.HasMGFUpperBoundAt.of_map
      (measurable_pi_apply (0 : Fin 1)).aemeasurable hfamilyMap
  have hpoint : forall trajectories : Fin 1 ->
      State × StepTrace Action State mdp.horizon,
      Zbatch (batchMap trajectories) = Ztrace (eval0 trajectories) := by
    intro trajectories
    simp only [Zbatch, Ztrace, eval0, Function.eval, batchMap]
    rw [EpisodeBatch.cumulativeDeterministicGapInnovation_episodeBatchOfTrajectories
      mdp defaultState table feature hhorizon trajectories]
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
    (EpisodeBatch.measurable_cumulativeDeterministicGapInnovation
      defaultState table feature |>.const_mul tilt).sub measurable_const
  have hid : Concentration.HasMGFUpperBoundAt id 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map
        (Zbatch ∘ batchMap)) :=
    (Concentration.HasMGFUpperBoundAt.id_map_iff
      (hZbatchMeas.comp hbatchMeas).aemeasurable).2 hcomposed
  unfold MarkovPolicy.iidEpisodeBatchMeasure
  apply (Concentration.HasMGFUpperBoundAt.id_map_iff
    hZbatchMeas.aemeasurable).1
  rw [Measure.map_map hZbatchMeas hbatchMeas]
  exact hid

end DeterministicMarkovPolicyTable

namespace MarkovPolicy

omit [Nonempty State] [Nonempty Action] in
/-- The exact one-episode batch image retains the stage-resolved MGF. -/
theorem iidEpisodeBatchMeasure_one_cumulativeTransitionGapInnovation_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (defaultState : State) (hhorizon : 0 < mdp.horizon)
    (feature : Fin mdp.horizon -> State -> Real)
    (hfeature : forall stage nextState,
      feature stage nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun batch : EpisodeBatch mdp 1 =>
        tilt * batch.cumulativeTransitionGapInnovation defaultState policy feature -
          (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8)
      1 0 (policy.iidEpisodeBatchMeasure initialState 1) := by
  let Ztrace : State × StepTrace Action State mdp.horizon -> Real :=
    fun trajectory =>
      tilt * mdp.sampledCumulativeTransitionGapInnovationFrom policy feature
          mdp.horizon le_rfl trajectory.1 trajectory.2 -
        (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
    tilt * batch.cumulativeTransitionGapInnovation defaultState policy feature -
      (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
  let eval0 : (Fin 1 -> State × StepTrace Action State mdp.horizon) ->
      State × StepTrace Action State mdp.horizon := Function.eval 0
  let batchMap := mdp.episodeBatchOfTrajectories 1
  have htrace :=
    mdp.trajectoryMeasure_transitionGapInnovation_compensated_hasMGFUpperBoundAt
      policy initialState feature hfeature tilt
  have hfamilyMap : Concentration.HasMGFUpperBoundAt Ztrace 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map eval0) := by
    rw [policy.iidTrajectoryFamilyMeasure_map_eval initialState (0 : Fin 1)]
    exact htrace
  have hfamily : Concentration.HasMGFUpperBoundAt (Ztrace ∘ eval0) 1 0
      (policy.iidTrajectoryFamilyMeasure initialState 1) :=
    Concentration.HasMGFUpperBoundAt.of_map
      (measurable_pi_apply (0 : Fin 1)).aemeasurable hfamilyMap
  have hpoint : forall trajectories : Fin 1 ->
      State × StepTrace Action State mdp.horizon,
      Zbatch (batchMap trajectories) = Ztrace (eval0 trajectories) := by
    intro trajectories
    simp only [Zbatch, Ztrace, eval0, Function.eval, batchMap]
    rw [EpisodeBatch.cumulativeTransitionGapInnovation_episodeBatchOfTrajectories
      mdp defaultState policy feature hhorizon trajectories]
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
    (EpisodeBatch.measurable_cumulativeTransitionGapInnovation
      defaultState policy feature |>.const_mul tilt).sub measurable_const
  have hid : Concentration.HasMGFUpperBoundAt id 1 0
      ((policy.iidTrajectoryFamilyMeasure initialState 1).map
        (Zbatch ∘ batchMap)) :=
    (Concentration.HasMGFUpperBoundAt.id_map_iff
      (hZbatchMeas.comp hbatchMeas).aemeasurable).2 hcomposed
  unfold iidEpisodeBatchMeasure
  apply (Concentration.HasMGFUpperBoundAt.id_map_iff
    hZbatchMeas.aemeasurable).1
  rw [Measure.map_map hZbatchMeas hbatchMeas]
  exact hid

end MarkovPolicy

end BanditRLProof.FiniteHorizonRL
