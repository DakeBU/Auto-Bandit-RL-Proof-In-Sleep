import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeHoeffdingUCBVI

/-!
# Cross-stage cumulative transition rows for UCBVI-CH

UCBVI-CH pools every visit of a state-action pair across stages.  The earlier
foundation exposed the aggregate denominator `N_k(x,a)` but retained only the
stage-indexed transition numerator.  This module closes that structural gap:
it defines `N_k(x,a,y)`, proves that its row sum is exactly the aggregate visit
count, proves exact generated-prefix and successor identities, and normalizes
the row into a probability kernel with an explicit Dirac fallback at zero.

No concentration or regret conclusion is asserted here.
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

namespace TransitionCountSummary

/-- The UCBVI-CH numerator `N_k(x,a,y)`, pooled across every decision stage. -/
def aggregateTransitionCount
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (state : State) (action : Action) (nextState : State) : Nat :=
  ∑ stage : Fin mdp.horizon, summary stage state action nextState

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The complete pooled transition-count table is measurable. -/
theorem measurable_aggregateTransitionCount {mdp : MDP State Action} :
    Measurable fun summary : TransitionCountSummary mdp =>
      fun state action nextState =>
        summary.aggregateTransitionCount state action nextState := by
  refine measurable_pi_lambda _ fun state => ?_
  refine measurable_pi_lambda _ fun action => ?_
  refine measurable_pi_lambda _ fun nextState => ?_
  refine Finset.measurable_sum Finset.univ fun stage _ => ?_
  exact (measurable_pi_apply nextState).comp
    ((measurable_pi_apply action).comp
      ((measurable_pi_apply state).comp (measurable_pi_apply stage)))

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Pooling transition destinations gives exactly the pooled visit count. -/
theorem sum_aggregateTransitionCount_eq_aggregateVisitCount
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (state : State) (action : Action) :
    (∑ nextState : State,
        summary.aggregateTransitionCount state action nextState) =
      summary.aggregateVisitCount state action := by
  classical
  unfold aggregateTransitionCount aggregateVisitCount visitCount
  rw [Finset.sum_comm]

/-- The normalized pooled empirical row, with a Dirac fallback at zero visits. -/
noncomputable def aggregateEmpiricalTransitionPMF
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (state : State) (action : Action) : PMF State :=
  if hzero : summary.aggregateVisitCount state action = 0 then
    PMF.pure defaultState
  else
    PMF.ofFintype
      (fun nextState =>
        (summary.aggregateTransitionCount state action nextState : ENNReal) /
          (summary.aggregateVisitCount state action : ENNReal))
      (by
        have sum_div_aggregateVisitCount (states : Finset State) :
            (∑ nextState ∈ states,
                (summary.aggregateTransitionCount state action nextState : ENNReal) /
                  (summary.aggregateVisitCount state action : ENNReal)) =
              (∑ nextState ∈ states,
                  (summary.aggregateTransitionCount state action nextState : ENNReal)) /
                (summary.aggregateVisitCount state action : ENNReal) := by
          classical
          induction states using Finset.induction_on with
          | empty => simp
          | @insert nextState states hnext ih =>
              simp only [Finset.sum_insert hnext]
              rw [ih, ENNReal.add_div]
        have hsum :
            (∑ nextState : State,
                (summary.aggregateTransitionCount state action nextState : ENNReal)) =
              (summary.aggregateVisitCount state action : ENNReal) := by
          exact_mod_cast
            summary.sum_aggregateTransitionCount_eq_aggregateVisitCount state action
        rw [sum_div_aggregateVisitCount Finset.univ]
        rw [hsum]
        exact ENNReal.div_self (by exact_mod_cast hzero) (ENNReal.natCast_ne_top _))

@[simp]
theorem aggregateEmpiricalTransitionPMF_of_aggregateVisitCount_eq_zero
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (state : State) (action : Action)
    (hzero : summary.aggregateVisitCount state action = 0) :
    summary.aggregateEmpiricalTransitionPMF defaultState state action =
      PMF.pure defaultState := by
  simp [aggregateEmpiricalTransitionPMF, hzero]

theorem aggregateEmpiricalTransitionPMF_apply_of_aggregateVisitCount_pos
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (state : State) (action : Action) (nextState : State)
    (hpos : 0 < summary.aggregateVisitCount state action) :
    summary.aggregateEmpiricalTransitionPMF defaultState state action nextState =
      (summary.aggregateTransitionCount state action nextState : ENNReal) /
        (summary.aggregateVisitCount state action : ENNReal) := by
  simp [aggregateEmpiricalTransitionPMF, Nat.ne_of_gt hpos, PMF.ofFintype_apply]

/-- The pooled empirical transition kernel is stage-homogeneous. -/
noncomputable def aggregateEmpiricalTransitionKernel
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) : ProbabilityTheory.Kernel (State × Action) State :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun pair =>
    (summary.aggregateEmpiricalTransitionPMF
      defaultState pair.1 pair.2).toMeasure

theorem aggregateEmpiricalTransitionKernel_isMarkov
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) :
    ProbabilityTheory.IsMarkovKernel
      (summary.aggregateEmpiricalTransitionKernel defaultState) where
  isProbabilityMeasure pair := by
    change IsProbabilityMeasure
      ((summary.aggregateEmpiricalTransitionPMF
        defaultState pair.1 pair.2).toMeasure)
    infer_instance

end TransitionCountSummary

/-- The pooled transition numerator through one generated trajectory prefix. -/
def adaptiveCumulativeAggregateTransitionCountAt
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (state : State) (action : Action) (nextState : State) : Nat :=
  (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
    |>.aggregateTransitionCount state action nextState

omit [Nonempty State] [Nonempty Action] in
theorem measurable_adaptiveCumulativeAggregateTransitionCountAt
    {mdp : MDP State Action} {episodes : Nat} (round : Nat)
    (state : State) (action : Action) (nextState : State) :
    Measurable fun trajectory : EpisodeBatchTrajectory mdp episodes =>
      adaptiveCumulativeAggregateTransitionCountAt trajectory round
        state action nextState := by
  exact
    ((measurable_pi_apply nextState).comp
      ((measurable_pi_apply action).comp
        ((measurable_pi_apply state).comp
          TransitionCountSummary.measurable_aggregateTransitionCount))).comp
      (measurable_adaptiveCumulativeEmpiricalModelStateAt round).fst

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The pooled numerator is the literal episode-by-stage generated count. -/
theorem adaptiveCumulativeAggregateTransitionCountAt_eq_sum
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (state : State) (action : Action) (nextState : State) :
    adaptiveCumulativeAggregateTransitionCountAt trajectory round
        state action nextState =
      ∑ i : Fin (round + 1), ∑ stage : Fin mdp.horizon,
        (trajectory i).transitionCount stage state action nextState := by
  classical
  unfold adaptiveCumulativeAggregateTransitionCountAt
    TransitionCountSummary.aggregateTransitionCount
    adaptiveCumulativeEmpiricalModelStateAt
    EpisodeBatchPrefix.cumulativeEmpiricalModelState
    EpisodeBatchPrefix.cumulativeTransitionCountSummary
  rw [Finset.sum_comm]
  rfl

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Extending the prefix adds exactly one episode's pooled transition row. -/
theorem adaptiveCumulativeAggregateTransitionCountAt_succ
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (state : State) (action : Action) (nextState : State) :
    adaptiveCumulativeAggregateTransitionCountAt trajectory (round + 1)
        state action nextState =
      adaptiveCumulativeAggregateTransitionCountAt trajectory round
          state action nextState +
        ∑ stage : Fin mdp.horizon,
          (trajectory (round + 1)).transitionCount
            stage state action nextState := by
  rw [adaptiveCumulativeAggregateTransitionCountAt_eq_sum,
    adaptiveCumulativeAggregateTransitionCountAt_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- At every generated prefix the pooled numerator row sums to the denominator. -/
theorem sum_adaptiveCumulativeAggregateTransitionCountAt_eq_visitCountAt
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (state : State) (action : Action) :
    (∑ nextState : State,
        adaptiveCumulativeAggregateTransitionCountAt trajectory round
          state action nextState) =
      adaptiveCumulativeAggregateVisitCountAt trajectory round state action := by
  exact
    (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
      |>.sum_aggregateTransitionCount_eq_aggregateVisitCount state action

end BanditRLProof.FiniteHorizonRL
