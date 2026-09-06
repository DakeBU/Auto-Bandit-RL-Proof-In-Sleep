import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIOptimism

/-! Bellman optimism for every queried policy of the one recurrent source. -/

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

omit [Nonempty State] [Nonempty Action] in
/-- The planner fold and the statistical state use literally the same prefix
transition summary. -/
theorem cumulativeSummaryOfSequence_prefixTransitionSummaries_eq
    {mdp : MDP State Action}
    (trajectory : EpisodeBatchTrajectory mdp 1) (round : Nat) :
    cumulativeSummaryOfSequence
        (prefixTransitionSummaries
          (Preorder.frestrictLe round trajectory)) =
      (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1 := by
  funext stage state action nextState
  simp [cumulativeSummaryOfSequence, prefixTransitionSummaries,
    adaptiveCumulativeEmpiricalModelStateAt,
    EpisodeBatchPrefix.cumulativeEmpiricalModelState,
    EpisodeBatchPrefix.cumulativeTransitionCountSummary,
    EpisodeBatch.transitionCountSummary]

namespace AdaptiveEpisodeBatchSource

/-- Every finite Q-table fold through the first `n` actually generated
episodes is optimistic on the proved same-source event. -/
theorem recurrentQTableOfTrajectory_dominatesOptimal
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) :
    ∀ n, n <= episodes ->
      QDominatesOptimal mdp
        (recurrentQTableOfSummaries mdp defaultState
          (scale (State := State) (Action := Action) mdp episodes delta) n
          (fun i => (trajectory i).transitionCountSummary)) := by
  intro n
  induction n with
  | zero =>
      intro _hn
      exact initialQTable_dominatesOptimal mdp (by
        intro state action
        rw [abs_of_nonneg (hrewardNonneg state action)]
        exact hrewardOne state action)
  | succ n ih =>
      intro hn
      have hnlt : n < episodes := by omega
      let round : Fin episodes := ⟨n, hnlt⟩
      let previous := recurrentQTableOfSummaries mdp defaultState
        (scale (State := State) (Action := Action) mdp episodes delta) n
        (fun i => (trajectory i).transitionCountSummary)
      let summary := cumulativeSummaryOfSequence
        (fun i : Fin (n + 1) => (trajectory i).transitionCountSummary)
      have hprevious : QDominatesOptimal mdp previous := by
        simpa [previous] using ih (by omega)
      have hsummary : summary =
          (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1 := by
        simpa [summary, round] using
          cumulativeSummaryOfSequence_prefixTransitionSummaries_eq
            trajectory n
      have hconfidence : HasOptimalTailConfidence mdp summary defaultState
          (scale (State := State) (Action := Action) mdp episodes delta) := by
        rw [hsummary]
        exact hasOptimalTailConfidence_of_not_mem_simultaneousTransitionFailureEvent
          source hhorizon hepisodes hdelta hdelta_le_one htrajectory
            defaultState round
      change QDominatesOptimal mdp
        (clippedQTable mdp previous summary defaultState
          (scale (State := State) (Action := Action) mdp episodes delta))
      exact clippedQTable_dominatesOptimal mdp previous summary defaultState
        (scale (State := State) (Action := Action) mdp episodes delta)
        hrewardNonneg hrewardOne hprevious hconfidence

/-- The generated successor episode selects an action whose actual recurrent
Q value dominates every optimal action value. -/
theorem recurrentSuccessor_selectedQ_ge_optimalQ
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (round : Fin episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    optimalQAt mdp stage state action <=
      recurrentQTableOfSummaries mdp defaultState
        (scale (State := State) (Action := Action) mdp episodes delta)
        (round + 1) (fun i => (trajectory i).transitionCountSummary)
        stage state
        (recurrentPolicyTableOfSummaries mdp defaultState
          (scale (State := State) (Action := Action) mdp episodes delta)
          (round + 1) (fun i => (trajectory i).transitionCountSummary)
          stage state) := by
  let table := recurrentQTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)
    (round + 1) (fun i => (trajectory i).transitionCountSummary)
  have hdom := recurrentQTableOfTrajectory_dominatesOptimal source hhorizon
    hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne htrajectory
      defaultState (round + 1) (by omega)
  exact (hdom stage state action).trans
    (FiniteRealArgmax.score_le_choose (table stage state) action)

end AdaptiveEpisodeBatchSource

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
