import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIOptimalTailAlignment

/-! Bellman optimism of one clipped recurrent UCBVI-CH update. -/

open MeasureTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveCumulativeHoeffdingUCBVI

noncomputable def optimalQAt
    (mdp : MDP State Action) (stage : Fin mdp.horizon)
    (state : State) (action : Action) : Real :=
  mdp.bellmanQ
    (mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt))
    state action

def QDominatesOptimal (mdp : MDP State Action) (table : QTable mdp) : Prop :=
  ∀ stage state action, optimalQAt mdp stage state action <=
    table stage state action

/-- Bounded rewards imply every optimal action value is at most `H`. -/
theorem optimalQAt_le_horizon
    (mdp : MDP State Action)
    (hreward : ∀ state action, |mdp.reward state action| <= 1)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    optimalQAt mdp stage state action <= (mdp.horizon : Real) := by
  have htail := mdp.optimalPolicy.valueRemaining_abs_le_of_rewardBound
    (1 : NNReal) (by simpa using hreward)
    (mdp.horizon - (stage + 1)) (Nat.sub_le _ _) state
  have htransition :
      mdp.transitionValue
          (mdp.optimalValueAt (stage + 1)
            (Nat.succ_le_of_lt stage.isLt)) state action <=
        (mdp.horizon - (stage + 1) : Nat) := by
    have hpoint : ∀ nextState,
        mdp.optimalValueAt (stage + 1)
              (Nat.succ_le_of_lt stage.isLt) nextState <=
          (mdp.horizon - (stage + 1) : Nat) := by
      intro nextState
      rw [← mdp.optimalPolicy_valueAt_eq_optimalValueAt]
      change mdp.optimalPolicy.valueRemaining
          (mdp.horizon - (stage + 1)) _ nextState <= _
      exact (le_abs_self _).trans (by
        simpa using (mdp.optimalPolicy.valueRemaining_abs_le_of_rewardBound
          (1 : NNReal) (by simpa using hreward)
          (mdp.horizon - (stage + 1)) (Nat.sub_le _ _) nextState))
    exact mdp.transitionValue_mono hpoint state action |>.trans (by
      simp [MDP.transitionValue])
  unfold optimalQAt MDP.bellmanQ
  have hre := (le_abs_self (mdp.reward state action)).trans
    (hreward state action)
  norm_num at hre
  have hhorizonPos : 0 < mdp.horizon := Nat.pos_of_ne_zero (by
    intro hzero
    have : stage.val < 0 := by simpa [hzero] using stage.isLt
    omega)
  have hstageCast : ((mdp.horizon - (stage + 1) : Nat) : Real) <=
      (mdp.horizon : Real) - 1 := by
    have hnat : mdp.horizon - (stage + 1) <= mdp.horizon - 1 := by omega
    have hcast : ((mdp.horizon - (stage + 1) : Nat) : Real) <=
        ((mdp.horizon - 1 : Nat) : Real) := by exact_mod_cast hnat
    rw [Nat.cast_sub (by omega : 1 <= mdp.horizon), Nat.cast_one] at hcast
    exact hcast
  linarith

/-- The all-`H` initialization is optimistic. -/
theorem initialQTable_dominatesOptimal
    (mdp : MDP State Action)
    (hreward : ∀ state action, |mdp.reward state action| <= 1) :
    QDominatesOptimal mdp (initialQTable mdp) := by
  intro stage state action
  exact optimalQAt_le_horizon mdp hreward stage state action

/-- Statistical premise for one deterministic clipped update.  Downstream it
is discharged from the same-source finite event; it is kept abstract here so
the Bellman induction remains reusable and auditable. -/
def HasOptimalTailConfidence
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (bonusScale : Real) : Prop :=
  ∀ (stage : Fin mdp.horizon) state action,
    0 < summary.aggregateVisitCount state action ->
    |(∫ nextState,
          mdp.optimalValueAt (stage + 1)
              (Nat.succ_le_of_lt stage.isLt) nextState
            ∂summary.aggregateEmpiricalTransitionKernel defaultState
              (state, action)) -
        mdp.transitionValue
          (mdp.optimalValueAt (stage + 1)
            (Nat.succ_le_of_lt stage.isLt)) state action| <=
      bonusScale / Real.sqrt (summary.aggregateVisitCount state action)

/-- One clipped update preserves pointwise optimal-Q dominance. -/
theorem clippedQTable_dominatesOptimal
    (mdp : MDP State Action) (previousQ : QTable mdp)
    (summary : TransitionCountSummary mdp) (defaultState : State)
    (bonusScale : Real)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1)
    (hprevious : QDominatesOptimal mdp previousQ)
    (hconfidence : HasOptimalTailConfidence mdp summary defaultState bonusScale) :
    QDominatesOptimal mdp
      (clippedQTable mdp previousQ summary defaultState bonusScale) := by
  have hrewardAbs : ∀ state action, |mdp.reward state action| <= 1 := by
    intro state action
    rw [abs_of_nonneg (hrewardNonneg state action)]
    exact hrewardOne state action
  letI : ProbabilityTheory.IsMarkovKernel
      (summary.aggregateEmpiricalTransitionKernel defaultState) :=
    summary.aggregateEmpiricalTransitionKernel_isMarkov defaultState
  have hvalue : ∀ (remaining : Nat) (hremaining : remaining <= mdp.horizon)
      (state : State),
      mdp.optimalValueAt (mdp.horizon - remaining) (Nat.sub_le _ _) state <=
        clippedValueRemaining previousQ summary defaultState bonusScale
          remaining hremaining state := by
    intro remaining
    induction remaining with
    | zero =>
        intro hremaining state
        simp [clippedValueRemaining, mdp.optimalValueAt_horizon]
    | succ remaining ih =>
        intro hremaining state
        let stage := mdp.decisionStageRemaining remaining hremaining
        let optimalTail := mdp.optimalValueAt (stage + 1)
            (Nat.succ_le_of_lt stage.isLt)
        let empirical := summary.aggregateEmpiricalTransitionKernel defaultState
        let tail := clippedValueRemaining previousQ summary defaultState bonusScale
          remaining (by omega)
        let score : State -> Action -> Real := fun state action =>
          let count := summary.aggregateVisitCount state action
          if count = 0 then (mdp.horizon : Real)
          else min (previousQ stage state action)
            (min (mdp.horizon : Real)
              (mdp.reward state action +
                (∫ nextState, tail nextState ∂empirical (state, action)) +
                bonusScale / Real.sqrt count))
        let optimalAction := mdp.optimalAction optimalTail state
        have htail : ∀ nextState, optimalTail nextState <= tail nextState := by
          intro nextState
          have hi := ih (by omega) nextState
          have hstageTail : mdp.horizon - remaining = (stage : Nat) + 1 := by
            simp [stage, MDP.decisionStageRemaining]
            omega
          simpa only [optimalTail, tail, hstageTail] using hi
        have hscore : mdp.bellmanQ optimalTail state optimalAction <=
            score state optimalAction := by
          let count := summary.aggregateVisitCount state optimalAction
          by_cases hzero : count = 0
          · simp [score, count, hzero]
            exact optimalQAt_le_horizon mdp hrewardAbs stage state optimalAction
          · have hpos : 0 < count := Nat.pos_of_ne_zero hzero
            rw [show score state optimalAction =
                min (previousQ stage state optimalAction)
                  (min (mdp.horizon : Real)
                    (mdp.reward state optimalAction +
                      (∫ nextState, tail nextState ∂empirical
                        (state, optimalAction)) +
                      bonusScale / Real.sqrt count)) by
              simp [score, count, hzero]]
            apply le_min
            · simpa [optimalQAt, optimalTail] using
                hprevious stage state optimalAction
            apply le_min
            · exact optimalQAt_le_horizon mdp hrewardAbs stage state optimalAction
            · have hempirical :
                  (∫ nextState, optimalTail nextState
                      ∂empirical (state, optimalAction)) <=
                    ∫ nextState, tail nextState
                      ∂empirical (state, optimalAction) := by
                apply integral_mono
                · exact integrable_of_fintype _ _ (measurable_of_finite _)
                · exact integrable_of_fintype _ _ (measurable_of_finite _)
                · exact htail
              have hconf := hconfidence stage state optimalAction hpos
              rw [abs_le] at hconf
              unfold MDP.bellmanQ
              linarith [hconf.1]
        have hstageEq : mdp.horizon - (remaining + 1) = stage := by
          simp [stage, MDP.decisionStageRemaining]
        have hbellman := congrFun
          (mdp.optimalValueAt_bellman stage stage.isLt) state
        change mdp.optimalValueAt (mdp.horizon - (remaining + 1)) _ state <= _
        rw [show mdp.optimalValueAt (mdp.horizon - (remaining + 1)) _ state =
            mdp.bellmanQ optimalTail state optimalAction by
          simpa [hstageEq, MDP.optimalBellman, optimalTail, optimalAction] using hbellman]
        rw [clippedValueRemaining]
        change mdp.bellmanQ optimalTail state optimalAction <=
          score state (FiniteRealArgmax.choose (score state))
        exact hscore.trans (FiniteRealArgmax.score_le_choose _ optimalAction)
  intro stage state action
  let remaining := mdp.horizon - (stage + 1)
  have hremaining : remaining + 1 <= mdp.horizon := by
    dsimp [remaining]
    omega
  have hstageRemaining :
      mdp.decisionStageRemaining remaining hremaining = stage := by
    apply Fin.ext
    simp [remaining, MDP.decisionStageRemaining]
    omega
  rw [show clippedQTable mdp previousQ summary defaultState bonusScale
        stage state action =
      clippedQRemaining previousQ summary defaultState bonusScale
        remaining hremaining state action by
    rfl]
  let count := summary.aggregateVisitCount state action
  by_cases hzero : count = 0
  · rw [clippedQRemaining_of_aggregateVisitCount_eq_zero _ _ _ _ _ _ _ _ hzero]
    exact optimalQAt_le_horizon mdp hrewardAbs stage state action
  · have hpos : 0 < count := Nat.pos_of_ne_zero hzero
    rw [clippedQRemaining_of_aggregateVisitCount_pos _ _ _ _ _ _ _ _ hpos]
    apply le_min
    · simpa [optimalQAt, hstageRemaining] using hprevious stage state action
    apply le_min
    · exact optimalQAt_le_horizon mdp hrewardAbs stage state action
    · let optimalTail := mdp.optimalValueAt (stage + 1)
          (Nat.succ_le_of_lt stage.isLt)
      let tail := clippedValueRemaining previousQ summary defaultState bonusScale
          remaining (by omega)
      have htail : ∀ nextState, optimalTail nextState <= tail nextState := by
        intro nextState
        have hi := hvalue remaining (by omega) nextState
        have htailStage : mdp.horizon - remaining = (stage : Nat) + 1 := by
          dsimp [remaining]
          omega
        simpa only [optimalTail, tail, htailStage] using hi
      have hempirical :
          (∫ nextState, optimalTail nextState
              ∂summary.aggregateEmpiricalTransitionKernel defaultState
                (state, action)) <=
            ∫ nextState, tail nextState
              ∂summary.aggregateEmpiricalTransitionKernel defaultState
                (state, action) := by
        apply integral_mono
        · exact integrable_of_fintype _ _ (measurable_of_finite _)
        · exact integrable_of_fintype _ _ (measurable_of_finite _)
        · exact htail
      have hconf := hconfidence stage state action hpos
      rw [abs_le] at hconf
      unfold optimalQAt MDP.bellmanQ
      linarith [hconf.1]

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- A pooled state-action count through prefix `round` is at most the number
of observed episodes times `H`. -/
theorem adaptiveCumulativeAggregateVisitCountAt_le
    {mdp : MDP State Action}
    (trajectory : EpisodeBatchTrajectory mdp 1) (round : Nat)
    (state : State) (action : Action) :
    adaptiveCumulativeAggregateVisitCountAt trajectory round state action <=
      (round + 1) * mdp.horizon := by
  rw [adaptiveCumulativeAggregateVisitCountAt_eq_sum]
  calc
    (∑ i : Fin (round + 1), ∑ stage : Fin mdp.horizon,
        (trajectory i).visitCount stage state action) <=
      ∑ _i : Fin (round + 1), mdp.horizon := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa [TransitionCountSummary.aggregateVisitCount,
          EpisodeBatch.transitionCountSummary_visitCount] using
          (trajectory i).aggregateVisitCount_le_horizon state action
    _ = (round + 1) * mdp.horizon := by simp [mul_comm]

namespace AdaptiveEpisodeBatchSource

/-- The same-source joint event discharges the complete scalar confidence
contract for the exact pooled summary at a queried positive prefix. -/
theorem hasOptimalTailConfidence_of_not_mem_simultaneousTransitionFailureEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (round : Fin episodes) :
    HasOptimalTailConfidence mdp
      (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1 defaultState
      (scale (State := State) (Action := Action) mdp episodes delta) := by
  intro stage state action hpos
  let count := adaptiveCumulativeAggregateVisitCountAt trajectory round state action
  have hcountPos : 0 < count := by simpa [count] using hpos
  have hcountRound : count <= (round + 1) * mdp.horizon :=
    adaptiveCumulativeAggregateVisitCountAt_le trajectory round state action
  have hroundEpisodes : round + 1 <= episodes := round.isLt
  have hcountGlobal : count <= episodes * mdp.horizon :=
    hcountRound.trans (Nat.mul_le_mul_right mdp.horizon hroundEpisodes)
  let countIndex : Fin (episodes * mdp.horizon) :=
    ⟨count - 1, by omega⟩
  let index : OptimalTailIndex mdp episodes :=
    { round := round
      stage := stage
      state := state
      action := action
      count := countIndex }
  have hactual : adaptiveCumulativeAggregateVisitCountAt trajectory index.round
      index.state index.action = index.count + 1 := by
    simp [index, countIndex, count]
    omega
  have hsharp := abs_empiricalTransition_optimalValue_sub_lt
    source htrajectory defaultState index hactual
  have hlogNonneg := logFactor_nonneg
    (State := State) (Action := Action) mdp episodes delta
  have hhorizonReal : 0 < (mdp.horizon : Real) := by exact_mod_cast hhorizon
  have hsqrtPos : 0 < Real.sqrt (count : Real) := by
    apply Real.sqrt_pos.2
    exact_mod_cast hcountPos
  have hindexCast : ((index.count + 1 : Nat) : Real) = count := by
    norm_cast
    simpa [index, count] using hactual.symm
  rw [hindexCast] at hsharp
  have hscale :
      2 * (mdp.horizon : Real) *
          logFactor (State := State) (Action := Action) mdp episodes delta /
          Real.sqrt count <=
        scale (State := State) (Action := Action) mdp episodes delta /
          Real.sqrt count := by
    apply (div_le_div_iff_of_pos_right hsqrtPos).2
    unfold scale
    nlinarith
  simpa [count] using hsharp.le.trans hscale

end AdaptiveEpisodeBatchSource

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
