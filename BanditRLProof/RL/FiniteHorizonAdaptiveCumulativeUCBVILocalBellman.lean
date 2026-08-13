import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVICoordinateAlignment

/-!
# Local Bellman recursion for one recurrent UCBVI update

The declarations in this file are deterministic.  The following generated
source layer discharges their two model-error inputs from the compiled joint
transition event.
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

/-- Transport the proof-indexed chronological optimal value across a stage
equality. -/
theorem optimalValueAt_eq_of_eq
    (mdp : MDP State Action) {left right : Nat}
    (hleft : left <= mdp.horizon) (hright : right <= mdp.horizon)
    (h : left = right) :
    mdp.optimalValueAt left hleft = mdp.optimalValueAt right hright := by
  subst right
  rfl

/-- Nonnegative rewards give a nonnegative optimal finite-horizon value. -/
theorem optimalValueAt_nonneg_of_reward_nonneg
    (mdp : MDP State Action)
    (hreward : forall state action, 0 <= mdp.reward state action)
    (stage : Nat) (hstage : stage <= mdp.horizon) (state : State) :
    0 <= mdp.optimalValueAt stage hstage state := by
  rw [← mdp.optimalPolicy_valueAt_eq_optimalValueAt]
  exact mdp.optimalPolicy.valueRemaining_nonneg_of_reward_nonneg hreward
    (mdp.horizon - stage) (Nat.sub_le _ _) state

end MDP

namespace AdaptiveCumulativeHoeffdingUCBVI

theorem decisionStageRemaining_succ_eq
    (mdp : MDP State Action) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) :
    (mdp.decisionStageRemaining remaining hremaining : Nat) + 1 =
      mdp.horizon - remaining := by
  simp [MDP.decisionStageRemaining]
  omega

/-- Transport the proof-indexed clipped Q surface across equality of the
remaining-horizon coordinate. -/
theorem clippedQRemaining_eq_of_eq
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) {left right : Nat}
    (hleft : left + 1 <= mdp.horizon)
    (hright : right + 1 <= mdp.horizon) (h : left = right) :
    clippedQRemaining previousQ summary defaultState bonusScale left hleft =
      clippedQRemaining previousQ summary defaultState bonusScale right hright := by
  subst right
  rfl

/-- The selected value in the backward recursion is the selected entry of the
chronological clipped Q table. -/
theorem clippedValueRemaining_succ_eq_selectedQ
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    clippedValueRemaining previousQ summary defaultState bonusScale
        (remaining + 1) hremaining state =
      clippedQRemaining previousQ summary defaultState bonusScale remaining
        hremaining state
        (clippedPolicyTable mdp previousQ summary defaultState bonusScale
          (mdp.decisionStageRemaining remaining hremaining) state) := by
  let stage := mdp.decisionStageRemaining remaining hremaining
  let q : Action -> Real := fun action =>
    clippedQRemaining previousQ summary defaultState bonusScale remaining
      hremaining state action
  have hq (action : Action) :
      clippedQTable mdp previousQ summary defaultState bonusScale
          stage state action = q action := by
    unfold clippedQTable
    change clippedQRemaining previousQ summary defaultState bonusScale
      (mdp.horizon - (stage.val + 1)) _ state action = q action
    have hinverse : mdp.horizon - (stage.val + 1) = remaining := by
      simp [stage, MDP.decisionStageRemaining]
      omega
    exact congrFun (congrFun
      (clippedQRemaining_eq_of_eq previousQ summary defaultState bonusScale
        _ hremaining hinverse) state) action
  have hchoice :
      FiniteRealArgmax.choose
          (fun action => clippedQTable mdp previousQ summary defaultState
            bonusScale stage state action) =
        FiniteRealArgmax.choose q := by
    congr 1
    funext action
    exact hq action
  simp only [clippedValueRemaining]
  change q (FiniteRealArgmax.choose q) =
    q (clippedPolicyTable mdp previousQ summary defaultState bonusScale
      stage state)
  unfold clippedPolicyTable
  rw [hchoice]

/-- Every entry of one clipped Q update is at most `H`. -/
theorem clippedQTable_le_horizon
    (mdp : MDP State Action) (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    clippedQTable mdp previousQ summary defaultState bonusScale
        stage state action <= (mdp.horizon : Real) := by
  unfold clippedQTable
  unfold clippedQRemaining
  dsimp only
  split_ifs with hzero
  · exact le_rfl
  · exact (min_le_right _ _).trans (min_le_left _ _)

/-- Clipping makes every selected upper value at most `H`, independently of
whether the statistical event holds. -/
theorem clippedValueRemaining_le_horizon
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon) (state : State) :
    clippedValueRemaining previousQ summary defaultState bonusScale
        remaining hremaining state <= (mdp.horizon : Real) := by
  cases remaining with
  | zero => simp [clippedValueRemaining]
  | succ remaining =>
      rw [clippedValueRemaining_succ_eq_selectedQ]
      unfold clippedQRemaining
      dsimp only
      split_ifs with hzero
      · exact le_rfl
      · exact (min_le_right _ _).trans (min_le_left _ _)

/-- Pointwise optimal-Q dominance implies that the selected clipped value
dominates the optimal value at the matching chronological stage. -/
theorem optimalValueAt_le_clippedValueRemaining
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real)
    (hdominates : QDominatesOptimal mdp
      (clippedQTable mdp previousQ summary defaultState bonusScale))
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) :
    mdp.optimalValueAt (mdp.horizon - remaining) (Nat.sub_le _ _ ) state <=
      clippedValueRemaining previousQ summary defaultState bonusScale
        remaining hremaining state := by
  cases remaining with
  | zero =>
      simp [clippedValueRemaining, mdp.optimalValueAt_horizon]
  | succ remaining =>
      let stage := mdp.decisionStageRemaining remaining hremaining
      let tail := mdp.optimalValueAt (stage + 1)
        (Nat.succ_le_of_lt stage.isLt)
      let optimalAction := mdp.optimalAction tail state
      let selected := clippedPolicyTable mdp previousQ summary defaultState
        bonusScale stage state
      have hstage : mdp.horizon - (remaining + 1) = stage := by
        rfl
      have hopt : mdp.optimalValueAt stage (Nat.le_of_lt stage.isLt) state =
          optimalQAt mdp stage state optimalAction := by
        rw [mdp.optimalValueAt_bellman stage stage.isLt]
        rfl
      have hentry := hdominates stage state optimalAction
      have hselected := clippedQTable_le_selected mdp previousQ summary
        defaultState bonusScale stage state optimalAction
      have htarget :
          mdp.optimalValueAt (mdp.horizon - (remaining + 1))
              (Nat.sub_le _ _) state =
            optimalQAt mdp stage state optimalAction := by
        calc
          mdp.optimalValueAt (mdp.horizon - (remaining + 1))
              (Nat.sub_le _ _) state =
              mdp.optimalValueAt stage (Nat.le_of_lt stage.isLt) state := by
            congr 2
          _ = optimalQAt mdp stage state optimalAction := hopt
      rw [htarget]
      rw [clippedValueRemaining_succ_eq_selectedQ]
      have hq :
          clippedQTable mdp previousQ summary defaultState bonusScale
              stage state selected =
            clippedQRemaining previousQ summary defaultState bonusScale
              remaining hremaining state selected := by
        unfold clippedQTable
        change clippedQRemaining previousQ summary defaultState bonusScale
          (mdp.horizon - (stage.val + 1)) _ state selected = _
        have hinverse : mdp.horizon - (stage.val + 1) = remaining := by
          simp [stage, MDP.decisionStageRemaining]
          omega
        exact congrFun (congrFun
          (clippedQRemaining_eq_of_eq previousQ summary defaultState bonusScale
            _ hremaining hinverse) state) selected
      change optimalQAt mdp stage state optimalAction <=
        clippedQRemaining previousQ summary defaultState bonusScale remaining
          hremaining state selected
      exact (hentry.trans hselected).trans_eq hq

/-- At a positive actual count, the selected clipped value minus the selected
policy value propagates through the true transition kernel, plus exactly the
empirical-model error and the configured bonus. -/
theorem clippedValueRemaining_sub_policyValueRemaining_le_of_pos
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale modelError : Real) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State)
    (hpos : 0 < summary.aggregateVisitCount state
      (clippedPolicyTable mdp previousQ summary defaultState bonusScale
        (mdp.decisionStageRemaining remaining hremaining) state))
    (hmodel :
      (∫ nextState,
          clippedValueRemaining previousQ summary defaultState bonusScale
              remaining (by omega) nextState
        ∂summary.aggregateEmpiricalTransitionKernel defaultState
          (state,
            clippedPolicyTable mdp previousQ summary defaultState bonusScale
              (mdp.decisionStageRemaining remaining hremaining) state)) -
        mdp.transitionValue
          (clippedValueRemaining previousQ summary defaultState bonusScale
            remaining (by omega)) state
          (clippedPolicyTable mdp previousQ summary defaultState bonusScale
            (mdp.decisionStageRemaining remaining hremaining) state) <=
        modelError) :
    clippedValueRemaining previousQ summary defaultState bonusScale
          (remaining + 1) hremaining state -
        (clippedPolicyTable mdp previousQ summary defaultState bonusScale
          |>.toMarkovPolicy).valueRemaining (remaining + 1) hremaining state <=
      mdp.transitionValue
          (fun nextState =>
            clippedValueRemaining previousQ summary defaultState bonusScale
                remaining (by omega) nextState -
              (clippedPolicyTable mdp previousQ summary defaultState bonusScale
                |>.toMarkovPolicy).valueRemaining remaining (by omega) nextState)
          state
          (clippedPolicyTable mdp previousQ summary defaultState bonusScale
            (mdp.decisionStageRemaining remaining hremaining) state) +
        modelError +
        bonusScale /
          Real.sqrt (summary.aggregateVisitCount state
            (clippedPolicyTable mdp previousQ summary defaultState bonusScale
              (mdp.decisionStageRemaining remaining hremaining) state)) := by
  let stage := mdp.decisionStageRemaining remaining hremaining
  let table := clippedPolicyTable mdp previousQ summary defaultState bonusScale
  let selected := table stage state
  let upperTail := clippedValueRemaining previousQ summary defaultState bonusScale
      remaining (by omega)
  let policy := table.toMarkovPolicy
  let policyTail := policy.valueRemaining remaining (by omega)
  let count := summary.aggregateVisitCount state selected
  have hq := clippedQRemaining_of_aggregateVisitCount_pos previousQ summary
    defaultState bonusScale remaining hremaining state selected hpos
  have hupper :
      clippedValueRemaining previousQ summary defaultState bonusScale
          (remaining + 1) hremaining state <=
        mdp.reward state selected +
          (∫ nextState, upperTail nextState
            ∂summary.aggregateEmpiricalTransitionKernel defaultState
              (state, selected)) +
          bonusScale / Real.sqrt count := by
    rw [clippedValueRemaining_succ_eq_selectedQ, hq]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hpolicy :
      policy.valueRemaining (remaining + 1) hremaining state =
        mdp.reward state selected +
          mdp.transitionValue policyTail state selected := by
    rw [MarkovPolicy.valueRemaining]
    change policy.bellman stage policyTail state = _
    unfold MarkovPolicy.bellman policy
    unfold DeterministicMarkovPolicyTable.toMarkovPolicy
    rw [ProbabilityTheory.Kernel.deterministic_apply]
    rw [integral_dirac']
    · rfl
    · exact
        ((mdp.measurable_bellmanQ (measurable_of_finite policyTail)).comp
          (measurable_const.prodMk measurable_id)).stronglyMeasurable
  have htransitionSub :
      mdp.transitionValue upperTail state selected -
          mdp.transitionValue policyTail state selected =
        mdp.transitionValue (fun nextState =>
          upperTail nextState - policyTail nextState) state selected := by
    unfold MDP.transitionValue
    have hupperInt : Integrable upperTail (mdp.transition (state, selected)) :=
      integrable_of_fintype _ _ (measurable_of_finite _)
    have hpolicyInt : Integrable policyTail (mdp.transition (state, selected)) :=
      integrable_of_fintype _ _ (measurable_of_finite _)
    rw [integral_sub hupperInt hpolicyInt]
  change _ <= _
  rw [hpolicy]
  change _ <= mdp.transitionValue
      (fun nextState => upperTail nextState - policyTail nextState)
      state selected + modelError + bonusScale / Real.sqrt count
  rw [← htransitionSub]
  have hmodel' :
      (∫ nextState, upperTail nextState
        ∂summary.aggregateEmpiricalTransitionKernel defaultState
          (state, selected)) -
        mdp.transitionValue upperTail state selected <= modelError := by
    simpa [upperTail, selected, table, stage] using hmodel
  linarith

/-- Bellman gap between one clipped recurrent value surface and the policy
selected by that same surface.  Naming this exact difference keeps the
generated-source recursion readable without hiding either policy identity. -/
noncomputable def clippedPolicyGapRemaining
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon) (state : State) : Real :=
  clippedValueRemaining previousQ summary defaultState bonusScale remaining
      hremaining state -
    (clippedPolicyTable mdp previousQ summary defaultState bonusScale
      |>.toMarkovPolicy).valueRemaining remaining hremaining state

/-- The deterministic positive-count recursion, expressed through the named
same-policy gap. -/
theorem clippedPolicyGapRemaining_le_of_pos
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale modelError : Real) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State)
    (hpos : 0 < summary.aggregateVisitCount state
      (clippedPolicyTable mdp previousQ summary defaultState bonusScale
        (mdp.decisionStageRemaining remaining hremaining) state))
    (hmodel :
      (∫ nextState,
          clippedValueRemaining previousQ summary defaultState bonusScale
              remaining (by omega) nextState
        ∂summary.aggregateEmpiricalTransitionKernel defaultState
          (state,
            clippedPolicyTable mdp previousQ summary defaultState bonusScale
              (mdp.decisionStageRemaining remaining hremaining) state)) -
        mdp.transitionValue
          (clippedValueRemaining previousQ summary defaultState bonusScale
            remaining (by omega)) state
          (clippedPolicyTable mdp previousQ summary defaultState bonusScale
            (mdp.decisionStageRemaining remaining hremaining) state) <=
        modelError) :
    clippedPolicyGapRemaining previousQ summary defaultState bonusScale
        (remaining + 1) hremaining state <=
      mdp.transitionValue
          (clippedPolicyGapRemaining previousQ summary defaultState bonusScale
            remaining (by omega))
          state
          (clippedPolicyTable mdp previousQ summary defaultState bonusScale
            (mdp.decisionStageRemaining remaining hremaining) state) +
        modelError + bonusScale /
          Real.sqrt (summary.aggregateVisitCount state
            (clippedPolicyTable mdp previousQ summary defaultState bonusScale
              (mdp.decisionStageRemaining remaining hremaining) state)) := by
  simpa only [clippedPolicyGapRemaining] using
    clippedValueRemaining_sub_policyValueRemaining_le_of_pos previousQ summary
      defaultState bonusScale modelError remaining hremaining state hpos hmodel

namespace AdaptiveEpisodeBatchSource

/-- On the same generated transition event, the model error of the selected
clipped continuation is self-bounded by the true propagated policy-value gap.
The other two terms are the sharp optimal-tail coordinate and the harmonic
Bernstein correction. -/
theorem selectedUpperTransitionModelError_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {logBudget : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (htrajectory : trajectory ∉
      simultaneousTransitionFailureEvent source episodes logBudget)
    (defaultState : State) (round : Fin episodes)
    (previousQ : QTable mdp) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State)
    (count : Fin (episodes * mdp.horizon))
    (hactual : adaptiveCumulativeAggregateVisitCountAt trajectory round state
        (clippedPolicyTable mdp previousQ
          (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
          defaultState (scale (State := State) (Action := Action)
            mdp episodes delta)
          (mdp.decisionStageRemaining remaining hremaining) state) = count + 1)
    (hdominates : QDominatesOptimal mdp
      (clippedQTable mdp previousQ
        (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
        defaultState (scale (State := State) (Action := Action)
          mdp episodes delta)))
    (hhorizon : 0 < mdp.horizon)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hlog : 0 <= logBudget) :
    (∫ nextState,
        clippedValueRemaining previousQ
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (scale (State := State) (Action := Action)
              mdp episodes delta)
            remaining (by omega) nextState
      ∂TransitionCountSummary.aggregateEmpiricalTransitionKernel
        (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
        defaultState
        (state,
          clippedPolicyTable mdp previousQ
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (scale (State := State) (Action := Action)
              mdp episodes delta)
            (mdp.decisionStageRemaining remaining hremaining) state)) -
      mdp.transitionValue
        (clippedValueRemaining previousQ
          (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
          defaultState (scale (State := State) (Action := Action)
            mdp episodes delta)
          remaining (by omega)) state
        (clippedPolicyTable mdp previousQ
          (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
          defaultState (scale (State := State) (Action := Action)
            mdp episodes delta)
          (mdp.decisionStageRemaining remaining hremaining) state) <=
      mdp.transitionValue
          (fun nextState =>
            clippedValueRemaining previousQ
                (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
                defaultState (scale (State := State) (Action := Action)
                  mdp episodes delta)
                remaining (by omega) nextState -
              ((clippedPolicyTable mdp previousQ
                (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
                defaultState (scale (State := State) (Action := Action)
                  mdp episodes delta)).toMarkovPolicy.valueRemaining
                    remaining (by omega) nextState))
          state
          (clippedPolicyTable mdp previousQ
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (scale (State := State) (Action := Action)
              mdp episodes delta)
            (mdp.decisionStageRemaining remaining hremaining) state) /
        (32 * mdp.horizon) +
      2 * mdp.horizon * logBudget / Real.sqrt (count + 1 : Nat) +
      66 * Fintype.card State * (mdp.horizon : Real) ^ 2 * logBudget /
        (count + 1 : Nat) := by
  let summary := (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
  let bonusScale := scale (State := State) (Action := Action) mdp episodes delta
  let stage := mdp.decisionStageRemaining remaining hremaining
  let table := clippedPolicyTable mdp previousQ summary defaultState bonusScale
  let selected := table stage state
  let upperTail := clippedValueRemaining previousQ summary defaultState bonusScale
    remaining (by omega)
  let policy := table.toMarkovPolicy
  let policyTail := policy.valueRemaining remaining (by omega)
  let optimalTail := mdp.optimalValueAt (stage + 1)
    (Nat.succ_le_of_lt stage.isLt)
  let optimalGap : State -> Real := fun nextState =>
    upperTail nextState - optimalTail nextState
  let policyGap : State -> Real := fun nextState =>
    upperTail nextState - policyTail nextState
  let empirical := summary.aggregateEmpiricalTransitionKernel defaultState
      (state, selected)
  letI : IsProbabilityMeasure empirical := by
    dsimp [empirical]
    exact (summary.aggregateEmpiricalTransitionKernel_isMarkov defaultState)
      |>.isProbabilityMeasure (state, selected)
  have hstageTail : (stage : Nat) + 1 = mdp.horizon - remaining :=
    decisionStageRemaining_succ_eq mdp remaining hremaining
  have hoptimalLe (nextState : State) :
      optimalTail nextState <= upperTail nextState := by
    have hbase := optimalValueAt_le_clippedValueRemaining previousQ summary
      defaultState bonusScale hdominates remaining (by omega) nextState
    have heq := mdp.optimalValueAt_eq_of_eq
      (Nat.succ_le_of_lt stage.isLt) (Nat.sub_le _ _) hstageTail
    simpa [optimalTail, upperTail] using
      (show optimalTail nextState =
          mdp.optimalValueAt (mdp.horizon - remaining) (Nat.sub_le _ _)
            nextState from congrFun heq nextState).le.trans hbase
  have hupperLe (nextState : State) :
      upperTail nextState <= (mdp.horizon : Real) :=
    clippedValueRemaining_le_horizon previousQ summary defaultState bonusScale
      remaining (by omega) nextState
  have hoptimalNonneg (nextState : State) : 0 <= optimalTail nextState :=
    mdp.optimalValueAt_nonneg_of_reward_nonneg hrewardNonneg _ _ nextState
  have hgap : forall nextState,
      optimalGap nextState ∈ Set.Icc (0 : Real) mdp.horizon := by
    intro nextState
    constructor
    · exact sub_nonneg.mpr (hoptimalLe nextState)
    · dsimp [optimalGap]
      linarith [hupperLe nextState, hoptimalNonneg nextState]
  have hpolicyLe (nextState : State) : policyTail nextState <= optimalTail nextState := by
    have hp := policy.valueAt_le_optimalValueAt (mdp.horizon - remaining)
      (Nat.sub_le _ _) nextState
    unfold MarkovPolicy.valueAt at hp
    have hinverse : mdp.horizon - (mdp.horizon - remaining) = remaining := by
      omega
    have hpEq := policy.valueRemaining_eq_of_eq
      (Nat.sub_le _ _) (Nat.le_of_succ_le hremaining) hinverse
    have hoEq := mdp.optimalValueAt_eq_of_eq (Nat.sub_le _ _)
      (Nat.succ_le_of_lt stage.isLt) hstageTail.symm
    rw [congrFun hpEq nextState] at hp
    exact hp.trans_eq (congrFun hoEq nextState)
  have hpropagate :
      mdp.transitionValue optimalGap state selected <=
        mdp.transitionValue policyGap state selected := by
    apply mdp.transitionValue_mono
    intro nextState
    dsimp [optimalGap, policyGap]
    linarith [hpolicyLe nextState]
  let optimalIndex : OptimalTailIndex mdp episodes :=
    { round := round, stage := stage, state := state, action := selected,
      count := count }
  have hoptAbs := abs_empiricalTransition_optimalValue_sub_lt source
    htrajectory defaultState optimalIndex hactual
  let coordinateBound :=
      mdp.transitionValue optimalGap state selected / (32 * mdp.horizon) +
        66 * Fintype.card State * (mdp.horizon : Real) ^ 2 * logBudget /
          (count + 1 : Nat)
  have hgapAbs :=
    abs_empiricalTransition_integral_sub_le_transitionValue_div_thirtyTwo_add
      source htrajectory defaultState round state selected count hactual optimalGap hgap
        hhorizon hlog
  have hsplit :
      (∫ nextState, upperTail nextState ∂empirical) -
          mdp.transitionValue upperTail state selected =
        ((∫ nextState, optimalTail nextState ∂empirical) -
            mdp.transitionValue optimalTail state selected) +
          ((∫ nextState, optimalGap nextState ∂empirical) -
            mdp.transitionValue optimalGap state selected) := by
    have hpoint : upperTail = fun nextState =>
        optimalTail nextState + optimalGap nextState := by
      funext nextState
      simp [optimalGap]
    rw [hpoint]
    unfold MDP.transitionValue
    rw [integral_add, integral_add]
    · ring
    all_goals exact integrable_of_fintype _ _ (measurable_of_finite _)
  have hmodel :
      (∫ nextState, upperTail nextState ∂empirical) -
          mdp.transitionValue upperTail state selected <=
        2 * mdp.horizon * logBudget / Real.sqrt (count + 1 : Nat) +
          coordinateBound := by
    rw [hsplit]
    have hopen :
        (∫ nextState, optimalTail nextState ∂empirical) -
            mdp.transitionValue optimalTail state selected <=
          2 * mdp.horizon * logBudget / Real.sqrt (count + 1 : Nat) :=
      le_trans (le_abs_self _) (le_of_lt (by
        simpa [optimalIndex, optimalTail, empirical, summary, selected, table,
          stage] using hoptAbs))
    have hgapUpper := (le_abs_self _).trans hgapAbs
    dsimp [coordinateBound]
    linarith
  change _ <= _
  change (∫ nextState, upperTail nextState ∂empirical) -
      mdp.transitionValue upperTail state selected <= _
  have hhorizonReal : 0 < (mdp.horizon : Real) := by exact_mod_cast hhorizon
  have hscaled :
      mdp.transitionValue optimalGap state selected / (32 * mdp.horizon) <=
        mdp.transitionValue policyGap state selected / (32 * mdp.horizon) :=
    (div_le_div_iff_of_pos_right
      (mul_pos (by norm_num) hhorizonReal)).2 hpropagate
  have hresult :
      (∫ nextState, upperTail nextState ∂empirical) -
          mdp.transitionValue upperTail state selected <=
        mdp.transitionValue policyGap state selected / (32 * mdp.horizon) +
          2 * mdp.horizon * logBudget / Real.sqrt (count + 1 : Nat) +
          66 * Fintype.card State * (mdp.horizon : Real) ^ 2 * logBudget /
            (count + 1 : Nat) := by
    calc
      _ <= 2 * mdp.horizon * logBudget / Real.sqrt (count + 1 : Nat) +
          coordinateBound := hmodel
      _ <= mdp.transitionValue policyGap state selected / (32 * mdp.horizon) +
          2 * mdp.horizon * logBudget / Real.sqrt (count + 1 : Nat) +
          66 * Fintype.card State * (mdp.horizon : Real) ^ 2 * logBudget /
            (count + 1 : Nat) := by
        dsimp [coordinateBound]
        linarith
  simpa [policyGap, upperTail, policyTail, policy, selected, table, stage,
    bonusScale, summary, empirical] using hresult

/-- Complete local UCBVI-CH recursion at an actual positive generated count.
The `7HL` planner bonus and the `2HL` sharp transition-value deviation combine
to `9HL`; the remaining coordinate term is self-bounded by the propagated
same-policy gap plus the explicit harmonic correction. -/
theorem selectedPolicyGap_le_of_actual_count
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (htrajectory : trajectory ∉
      simultaneousTransitionFailureEvent source episodes
        (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (round : Fin episodes)
    (previousQ : QTable mdp) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State)
    (count : Fin (episodes * mdp.horizon))
    (hactual : adaptiveCumulativeAggregateVisitCountAt trajectory round state
        (clippedPolicyTable mdp previousQ
          (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
          defaultState (scale (State := State) (Action := Action)
            mdp episodes delta)
          (mdp.decisionStageRemaining remaining hremaining) state) = count + 1)
    (hdominates : QDominatesOptimal mdp
      (clippedQTable mdp previousQ
        (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
        defaultState (scale (State := State) (Action := Action)
          mdp episodes delta)))
    (hhorizon : 0 < mdp.horizon)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action) :
    clippedPolicyGapRemaining previousQ
        (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
        defaultState (scale (State := State) (Action := Action)
          mdp episodes delta)
        (remaining + 1) hremaining state <=
      mdp.transitionValue
          (clippedPolicyGapRemaining previousQ
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (scale (State := State) (Action := Action)
              mdp episodes delta)
            remaining (by omega))
          state
          (clippedPolicyTable mdp previousQ
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (scale (State := State) (Action := Action)
              mdp episodes delta)
            (mdp.decisionStageRemaining remaining hremaining) state) +
        mdp.transitionValue
          (clippedPolicyGapRemaining previousQ
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (scale (State := State) (Action := Action)
              mdp episodes delta)
            remaining (by omega))
          state
          (clippedPolicyTable mdp previousQ
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (scale (State := State) (Action := Action)
              mdp episodes delta)
            (mdp.decisionStageRemaining remaining hremaining) state) /
            (32 * mdp.horizon) +
        9 * mdp.horizon *
            logFactor (State := State) (Action := Action) mdp episodes delta /
          Real.sqrt (count + 1 : Nat) +
        66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
            logFactor (State := State) (Action := Action) mdp episodes delta /
          (count + 1 : Nat) := by
  let summary := (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
  let bonusScale := scale (State := State) (Action := Action) mdp episodes delta
  let stage := mdp.decisionStageRemaining remaining hremaining
  let selected := clippedPolicyTable mdp previousQ summary defaultState
    bonusScale stage state
  let gap := clippedPolicyGapRemaining previousQ summary defaultState bonusScale
    remaining (by omega)
  have hcountEq : summary.aggregateVisitCount state selected = (count : Nat) + 1 := by
    simpa [summary, selected, stage, bonusScale] using hactual
  have hcountPos : 0 < summary.aggregateVisitCount state selected := by
    rw [hcountEq]
    omega
  have hmodel := selectedUpperTransitionModelError_le source htrajectory
    defaultState round previousQ remaining hremaining state count hactual
    hdominates hhorizon hrewardNonneg
      (logFactor_nonneg mdp episodes delta)
  have hlocal := clippedPolicyGapRemaining_le_of_pos previousQ summary
    defaultState bonusScale
    (mdp.transitionValue gap state selected / (32 * mdp.horizon) +
      2 * mdp.horizon *
          logFactor (State := State) (Action := Action) mdp episodes delta /
        Real.sqrt (count + 1 : Nat) +
      66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
          logFactor (State := State) (Action := Action) mdp episodes delta /
        (count + 1 : Nat))
    remaining hremaining state hcountPos (by
      simpa [gap, selected, stage, bonusScale, summary] using hmodel)
  rw [hcountEq] at hlocal
  have hlocal' :
      clippedPolicyGapRemaining previousQ summary defaultState bonusScale
          (remaining + 1) hremaining state <=
        mdp.transitionValue gap state selected +
          mdp.transitionValue gap state selected / (32 * mdp.horizon) +
          2 * mdp.horizon *
              logFactor (State := State) (Action := Action) mdp episodes delta /
            Real.sqrt (count + 1 : Nat) +
          66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
              logFactor (State := State) (Action := Action) mdp episodes delta /
            (count + 1 : Nat) +
          7 * mdp.horizon *
              logFactor (State := State) (Action := Action) mdp episodes delta /
            Real.sqrt (count + 1 : Nat) := by
    simpa [gap, selected, stage, bonusScale, summary, scale, add_assoc] using hlocal
  have hcombined :
      clippedPolicyGapRemaining previousQ summary defaultState bonusScale
          (remaining + 1) hremaining state <=
        mdp.transitionValue gap state selected +
          mdp.transitionValue gap state selected / (32 * mdp.horizon) +
          9 * mdp.horizon *
              logFactor (State := State) (Action := Action) mdp episodes delta /
            Real.sqrt (count + 1 : Nat) +
          66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
              logFactor (State := State) (Action := Action) mdp episodes delta /
            (count + 1 : Nat) := by
    calc
      _ <= mdp.transitionValue gap state selected +
            mdp.transitionValue gap state selected / (32 * mdp.horizon) +
            2 * mdp.horizon *
                logFactor (State := State) (Action := Action) mdp episodes delta /
              Real.sqrt (count + 1 : Nat) +
            66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
                logFactor (State := State) (Action := Action) mdp episodes delta /
              (count + 1 : Nat) +
            7 * mdp.horizon *
                logFactor (State := State) (Action := Action) mdp episodes delta /
              Real.sqrt (count + 1 : Nat) := hlocal'
      _ = _ := by ring
  simpa [gap, selected, stage, bonusScale, summary] using hcombined

end AdaptiveEpisodeBatchSource

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
