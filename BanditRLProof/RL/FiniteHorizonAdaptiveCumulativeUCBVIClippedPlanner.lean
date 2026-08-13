import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIAggregateTransition

/-!
# Previous-Q clipped recurrent UCBVI-CH planner

This module defines the actual recurrent planner used by the Chapter 9 route.
Coordinate zero uses the all-`H` initial Q table and its fixed finite argmax.
After observing coordinates `0,...,n`, the successor planner folds those exact
transition summaries, normalizes their cross-stage aggregate row, and applies
the backward recurrence

`Q = H` at zero count and
`Q = min Q_previous (min H (reward + P_hat V_next + 7 H L / sqrt N))`
at positive count.

The adaptive source below therefore contains no arbitrary uncharged initial
policy.  Its successor policy is a measurable function of the strict generated
prefix, and its batch kernel is exactly the one-episode trajectory law of that
selected policy.
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

namespace AdaptiveCumulativeHoeffdingUCBVI

/-- A chronological action-value table for all actual decision stages. -/
abbrev QTable (mdp : MDP State Action) :=
  Fin mdp.horizon -> State -> Action -> Real

/-- The UCBVI-CH initialization `Q_{0,h}(x,a)=H`. -/
def initialQTable (mdp : MDP State Action) : QTable mdp :=
  fun _stage _state _action => (mdp.horizon : Real)

/-- Sum a finite sequence of observed transition summaries coordinatewise. -/
def cumulativeSummaryOfSequence
    {mdp : MDP State Action} {n : Nat}
    (summaries : Fin n -> TransitionCountSummary mdp) :
    TransitionCountSummary mdp :=
  fun stage state action nextState =>
    ∑ i : Fin n, summaries i stage state action nextState

/--
The recursively selected clipped value with a given previous-episode Q table
and one pooled empirical transition model.  The index is decisions remaining;
its successor case uses the chronological stage `H-(remaining+1)`.
-/
noncomputable def clippedValueRemaining
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State -> Real
  | 0, _ => fun _state => 0
  | remaining + 1, hremaining =>
      let stage := mdp.decisionStageRemaining remaining hremaining
      let tail := clippedValueRemaining previousQ summary defaultState bonusScale
        remaining (by omega)
      let score : State -> Action -> Real := fun state action =>
        let count := summary.aggregateVisitCount state action
        if count = 0 then (mdp.horizon : Real)
        else
          min (previousQ stage state action)
            (min (mdp.horizon : Real)
              (mdp.reward state action +
                (∫ nextState, tail nextState ∂
                  summary.aggregateEmpiricalTransitionKernel defaultState
                    (state, action)) +
                bonusScale / Real.sqrt count))
      fun state =>
        score state
          (FiniteRealArgmax.choose (fun action => score state action))

/-- The action-value used at one remaining-horizon coordinate. -/
noncomputable def clippedQRemaining
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action) : Real :=
  let stage := mdp.decisionStageRemaining remaining hremaining
  let count := summary.aggregateVisitCount state action
  if count = 0 then (mdp.horizon : Real)
  else
    min (previousQ stage state action)
      (min (mdp.horizon : Real)
        (mdp.reward state action +
          (∫ nextState,
            clippedValueRemaining previousQ summary defaultState bonusScale
              remaining (by omega) nextState ∂
              summary.aggregateEmpiricalTransitionKernel defaultState
                (state, action)) +
          bonusScale / Real.sqrt count))

/-- The complete chronological Q table produced by one recurrent update. -/
noncomputable def clippedQTable
    (mdp : MDP State Action) (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) : QTable mdp :=
  fun stage =>
    clippedQRemaining previousQ summary defaultState bonusScale
      (mdp.horizon - (stage.val + 1)) (by omega)

@[simp]
theorem clippedQRemaining_of_aggregateVisitCount_eq_zero
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action)
    (hzero : summary.aggregateVisitCount state action = 0) :
    clippedQRemaining previousQ summary defaultState bonusScale
        remaining hremaining state action = (mdp.horizon : Real) := by
  simp [clippedQRemaining, hzero]

theorem clippedQRemaining_of_aggregateVisitCount_pos
    {mdp : MDP State Action} (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action)
    (hpos : 0 < summary.aggregateVisitCount state action) :
    clippedQRemaining previousQ summary defaultState bonusScale
        remaining hremaining state action =
      min (previousQ (mdp.decisionStageRemaining remaining hremaining)
          state action)
        (min (mdp.horizon : Real)
          (mdp.reward state action +
            (∫ nextState,
              clippedValueRemaining previousQ summary defaultState bonusScale
                remaining (by omega) nextState ∂
                summary.aggregateEmpiricalTransitionKernel defaultState
                  (state, action)) +
            bonusScale /
              Real.sqrt (summary.aggregateVisitCount state action))) := by
  simp [clippedQRemaining, Nat.ne_of_gt hpos]

/-- Fixed-enumeration argmax table of one recurrent Q update. -/
noncomputable def clippedPolicyTable
    (mdp : MDP State Action) (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) : DeterministicMarkovPolicyTable mdp :=
  fun stage state =>
    FiniteRealArgmax.choose
      (fun action =>
        clippedQTable mdp previousQ summary defaultState bonusScale
          stage state action)

/-- The selected recurrent action maximizes the actual clipped Q table. -/
theorem clippedQTable_le_selected
    (mdp : MDP State Action) (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    clippedQTable mdp previousQ summary defaultState bonusScale
        stage state action <=
      clippedQTable mdp previousQ summary defaultState bonusScale
        stage state
        (clippedPolicyTable mdp previousQ summary defaultState bonusScale
          stage state) := by
  exact FiniteRealArgmax.score_le_choose _ action

/-- Every recurrent selector is measurable on the finite state space. -/
theorem measurable_clippedPolicyTable
    (mdp : MDP State Action) (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real) (stage : Fin mdp.horizon) :
    Measurable
      (clippedPolicyTable mdp previousQ summary defaultState bonusScale stage) :=
  measurable_of_finite _

/-- Fold observed summaries into the genuine sequence of previous-Q updates. -/
noncomputable def recurrentQTableOfSummaries
    (mdp : MDP State Action) (defaultState : State) (bonusScale : Real) :
    (n : Nat) -> (Fin n -> TransitionCountSummary mdp) -> QTable mdp
  | 0, _summaries => initialQTable mdp
  | n + 1, summaries =>
      let previous := recurrentQTableOfSummaries mdp defaultState bonusScale n
        (fun i => summaries i.castSucc)
      let cumulative := cumulativeSummaryOfSequence summaries
      clippedQTable mdp previous cumulative defaultState bonusScale

/-- Policy table obtained after the same finite previous-Q fold. -/
noncomputable def recurrentPolicyTableOfSummaries
    (mdp : MDP State Action) (defaultState : State) (bonusScale : Real)
    (n : Nat) (summaries : Fin n -> TransitionCountSummary mdp) :
    DeterministicMarkovPolicyTable mdp :=
  fun stage state =>
    FiniteRealArgmax.choose
      (fun action =>
        recurrentQTableOfSummaries mdp defaultState bonusScale n summaries
          stage state action)

/-- Extract exactly the transition summaries stored in one finite prefix. -/
def prefixTransitionSummaries
    {mdp : MDP State Action} {episodes n : Nat}
    (history : EpisodeBatchPrefix mdp episodes n) :
    Fin (n + 1) -> TransitionCountSummary mdp :=
  fun i =>
    (history ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩)
      |>.transitionCountSummary

omit [Nonempty State] [Nonempty Action] in
theorem measurable_prefixTransitionSummaries
    {mdp : MDP State Action} {episodes n : Nat} :
    Measurable
      (prefixTransitionSummaries : EpisodeBatchPrefix mdp episodes n ->
        Fin (n + 1) -> TransitionCountSummary mdp) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact EpisodeBatch.measurable_transitionCountSummary.comp
    (measurable_pi_apply
      (⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩ : Finset.Iic n))

/-- Measurable strict-prefix selector for the recurrent generated source. -/
noncomputable def recurrentSuccessorTable
    {mdp : MDP State Action} {episodes : Nat}
    (defaultState : State) (bonusScale : Real) (n : Nat)
    (history : EpisodeBatchPrefix mdp episodes n) :
    DeterministicMarkovPolicyTable mdp :=
  recurrentPolicyTableOfSummaries mdp defaultState bonusScale (n + 1)
    (prefixTransitionSummaries history)

omit [Nonempty State] in
theorem measurable_recurrentSuccessorTable
    {mdp : MDP State Action} {episodes : Nat}
    (defaultState : State) (bonusScale : Real) (n : Nat) :
    Measurable
      (recurrentSuccessorTable (mdp := mdp) (episodes := episodes)
        defaultState bonusScale n) := by
  let summaries : EpisodeBatchPrefix mdp episodes n ->
      Fin (n + 1) -> TransitionCountSummary mdp :=
    prefixTransitionSummaries
  let table : (Fin (n + 1) -> TransitionCountSummary mdp) ->
      DeterministicMarkovPolicyTable mdp :=
    fun observed => recurrentPolicyTableOfSummaries mdp defaultState bonusScale
      (n + 1) observed
  have htable : Measurable table := by
    letI : MeasurableSingletonClass
        (Fin (n + 1) -> TransitionCountSummary mdp) :=
      Pi.instMeasurableSingletonClass
    refine measurable_pi_lambda _ fun stage => ?_
    refine measurable_pi_lambda _ fun state => ?_
    exact measurable_of_countable _
  exact htable.comp measurable_prefixTransitionSummaries

/-- The initial table is the fixed argmax of the all-`H` Q initialization. -/
noncomputable def recurrentInitialTable (mdp : MDP State Action) :
    DeterministicMarkovPolicyTable mdp :=
  fun stage state =>
    FiniteRealArgmax.choose
      (fun action => initialQTable mdp stage state action)

/--
Canonical one-episode recurrent UCBVI source.  It has no arbitrary initial
policy parameter: coordinate zero executes `recurrentInitialTable`; coordinate
`n+1` executes the fold of exactly the observed coordinates `0,...,n`.
-/
noncomputable def recurrentSource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta : Real) :
    AdaptiveEpisodeBatchSource mdp initialState 1 where
  initialPolicy := (recurrentInitialTable mdp).toMarkovPolicy
  successorPolicy n history :=
    (recurrentSuccessorTable defaultState
      (scale (State := State) (Action := Action) mdp episodes delta)
      n history).toMarkovPolicy
  batchKernel n :=
    (DeterministicMarkovPolicyTable.iidEpisodeBatchKernel initialState 1).comap
      (recurrentSuccessorTable defaultState
        (scale (State := State) (Action := Action) mdp episodes delta) n)
      (measurable_recurrentSuccessorTable defaultState
        (scale (State := State) (Action := Action) mdp episodes delta) n)
  batchKernel_isMarkov n := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      (measurable_recurrentSuccessorTable defaultState
        (scale (State := State) (Action := Action) mdp episodes delta) n)
  batchKernel_eq_iidEpisodeBatchMeasure n history := by
    rw [ProbabilityTheory.Kernel.comap_apply]
    rfl

/-- Coordinate zero uses the all-`H` initialized recurrent policy. -/
theorem recurrentSource_policyAt_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) :
    (recurrentSource mdp initialState defaultState episodes delta).policyAt
        trajectory 0 =
      (recurrentInitialTable mdp).toMarkovPolicy := by
  rfl

/-- Every successor policy is the exact strict-prefix previous-Q fold. -/
theorem recurrentSource_policyAt_succ
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    (recurrentSource mdp initialState defaultState episodes delta).policyAt
        trajectory (n + 1) =
      (recurrentSuccessorTable defaultState
        (scale (State := State) (Action := Action) mdp episodes delta) n
        (Preorder.frestrictLe n trajectory)).toMarkovPolicy := by
  rfl

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
