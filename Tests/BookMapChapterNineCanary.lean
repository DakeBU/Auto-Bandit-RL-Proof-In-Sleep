import BanditRLProof

/-!
# Book Map Chapter 9 canonical Hoeffding UCBVI-CH canary

This external canary keeps the full generated chain visible: finite-MDP
optimality, occupancy regret, cumulative state updates, aggregate transition
alignment, the previous-Q clipped recurrent planner, same-source confidence,
optimism, generated episode regret, counting, Bellman martingale control, the
frozen `20/250` high-probability terminal, and its `K H delta` expected
corollary.  The final two declarations are instantiated on a nondegenerate
two-state, two-action, horizon-two deterministic MDP with two generated
episodes and `delta = 1/2`.

This is only the known-reward Hoeffding UCBVI-CH scope.  It does not certify a
Bernstein/minimax, stochastic-reward, or realized-return UCBVI theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace BanditRLProof.BookMapChapterNineCanary

open FiniteHorizonRL
open FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI

universe u v

section FoundationAndGeneratedChain

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/-- Bellman optimality dominates every policy and is attained. -/
example (mdp : MDP State Action) :
    (∀ (policy : MarkovPolicy mdp) (stage : Nat)
      (hstage : stage <= mdp.horizon) (state : State),
        policy.valueAt stage hstage state <=
          mdp.optimalValueAt stage hstage state) ∧
      (∃ policy : MarkovPolicy mdp,
        ∀ (stage : Nat) (hstage : stage <= mdp.horizon),
          policy.valueAt stage hstage = mdp.optimalValueAt stage hstage) := by
  exact mdp.optimalValueAt_dominates_and_is_attained

/-- Occupancy regret is an expected policy-regret identity, not a sampled
return identity. -/
example (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState] :
    policy.expectedRegret initialState =
        policy.occupancyGapRemaining mdp.horizon le_rfl initialState ∧
      0 <= policy.expectedRegret initialState ∧
      mdp.optimalPolicy.expectedRegret initialState = 0 := by
  exact mdp.expectedRegret_eq_occupancyGap_nonneg_and_optimalPolicy_zero
    policy initialState

/-- Both transition counts and reward sums extend by the literal newly
generated coordinate. -/
example {mdp : MDP State Action} {batchSize : Nat}
    (trajectory : EpisodeBatchTrajectory mdp batchSize) (round : Nat)
    (stage : Fin mdp.horizon) (state nextState : State) (action : Action) :
    (adaptiveCumulativeEmpiricalModelStateAt trajectory (round + 1)).1
          stage state action nextState =
        (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            stage state action nextState +
          (trajectory (round + 1)).transitionCount
            stage state action nextState ∧
      (adaptiveCumulativeEmpiricalModelStateAt trajectory (round + 1)).2
          stage state action =
        (adaptiveCumulativeEmpiricalModelStateAt trajectory round).2
            stage state action +
          (trajectory (round + 1)).rewardSum stage state action := by
  exact ⟨adaptiveCumulativeEmpiricalModelStateAt_transitionCount_succ
      trajectory round stage state action nextState,
    adaptiveCumulativeEmpiricalModelStateAt_rewardSum_succ
      trajectory round stage state action⟩

/-- Aggregate transition numerator and aggregate visit denominator are the
same summary, including their exact row-sum alignment. -/
example {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (state : State) (action : Action) :
    (∑ nextState : State,
        summary.aggregateTransitionCount state action nextState) =
      summary.aggregateVisitCount state action := by
  exact summary.sum_aggregateTransitionCount_eq_aggregateVisitCount state action

/-- Positive-count recurrent Q is literally previous-Q clipping plus the
known reward, aggregate empirical transition value, and Hoeffding bonus. -/
example {mdp : MDP State Action} (previousQ : QTable mdp)
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
  exact clippedQRemaining_of_aggregateVisitCount_pos previousQ summary
    defaultState bonusScale remaining hremaining state action hpos

/-- The recurrent finite argmax table is measurable. -/
example (mdp : MDP State Action) (defaultState : State)
    (bonusScale : Real) (n : Nat) :
    Measurable
      (recurrentSuccessorTable (mdp := mdp) (episodes := 1)
        defaultState bonusScale n) := by
  exact measurable_recurrentSuccessorTable defaultState bonusScale n

/-- Generated episode `n+1` uses exactly the strict prefix through `n`. -/
example (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    (recurrentSource mdp initialState defaultState episodes delta).policyAt
        trajectory (n + 1) =
      (recurrentSuccessorTable defaultState
        (scale (State := State) (Action := Action) mdp episodes delta) n
        (Preorder.frestrictLe n trajectory)).toMarkovPolicy := by
  exact recurrentSource_policyAt_succ mdp initialState defaultState
    episodes delta trajectory n

/-- Same-source simultaneous singleton-Bernstein and optimal-tail confidence
has an explicit one-fifth failure budget. -/
example (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hreward : ∀ state action, |mdp.reward state action| <= 1) :
    let source := recurrentSource mdp initialState defaultState episodes delta
    source.trajectoryMeasure
        (AdaptiveEpisodeBatchSource.simultaneousTransitionFailureEvent
          source episodes
          (logFactor (State := State) (Action := Action)
            mdp episodes delta)) <= ENNReal.ofReal (delta / 5) := by
  exact recurrentSource_trajectoryMeasure_simultaneousTransitionFailureEvent_le_fifth
    mdp initialState defaultState episodes delta hhorizon hepisodes hdelta
      hdeltaOne hreward

/-- Outside that event, every strict-prefix recurrent Q table is optimistic. -/
example {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉
      AdaptiveEpisodeBatchSource.simultaneousTransitionFailureEvent source episodes
        (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) :
    ∀ n, n <= episodes →
      QDominatesOptimal mdp
        (recurrentQTableOfSummaries mdp defaultState
          (scale (State := State) (Action := Action) mdp episodes delta) n
          (fun i => (trajectory i).transitionCountSummary)) := by
  exact
    AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource.recurrentQTableOfTrajectory_dominatesOptimal
      source hhorizon hepisodes hdelta hdeltaOne hrewardNonneg hrewardOne
        htrajectory defaultState

/-- One generated successor episode is bounded by the actual canonical charge
plus its Bellman innovation on the same trajectory. -/
example {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1)
    (defaultState : State)
    (htrajectory : trajectory ∉
      AdaptiveEpisodeBatchSource.simultaneousTransitionFailureEvent
        (recurrentSource mdp initialState defaultState episodes delta) episodes
        (logFactor (State := State) (Action := Action) mdp episodes delta))
    (n : Nat) (hn : n + 1 < episodes) :
    generatedEpisodePseudoRegret
        (recurrentSource mdp initialState defaultState episodes delta)
        defaultState trajectory (n + 1) <=
      bellmanWeightCap *
        (successorCanonicalWeightedCharge mdp defaultState episodes delta
            trajectory n +
          recurrentBellmanInnovationProcess mdp defaultState episodes delta
            (n + 1) trajectory) := by
  exact AdaptiveEpisodeBatchSource.recurrentSource_generatedSuccessorPseudoRegret_le_charge_add_innovation
    initialState hhorizon hepisodes hdelta hdeltaOne hrewardNonneg hrewardOne
      defaultState htrajectory n hn

/-- The pathwise count ledger closes to the explicit square-root plus harmonic
charge bound. -/
example (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1) :
    totalGeneratedPairCharge mdp episodes delta trajectory <=
      18 * (mdp.horizon : Real) *
          logFactor (State := State) (Action := Action) mdp episodes delta *
          (Real.sqrt (totalSteps mdp episodes : Nat) *
            Real.sqrt ((Fintype.card State * Fintype.card Action : Nat) : Real)) +
        238 * (Fintype.card State : Real) ^ 2 *
          Fintype.card Action * (mdp.horizon : Real) ^ 2 *
          logFactor (State := State) (Action := Action)
            mdp episodes delta ^ 2 := by
  exact totalGeneratedPairCharge_le_explicit mdp episodes delta trajectory
    hhorizon hepisodes hdelta hdeltaOne

/-- The generated Bellman innovation uses its own recurrent trajectory law and
costs another one-fifth of the confidence budget. -/
example (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1) :
    let source := recurrentSource mdp initialState defaultState episodes delta
    source.trajectoryMeasure
        {trajectory |
          bellmanInnovationThreshold (State := State) (Action := Action)
              mdp episodes delta <=
            (Finset.range episodes).sum (fun round =>
              recurrentBellmanInnovationProcess mdp defaultState episodes delta
                round trajectory)} <= ENNReal.ofReal (delta / 5) := by
  exact recurrentSource_trajectoryMeasure_bellmanInnovation_sum_ge_threshold_le_fifth
    mdp initialState defaultState episodes delta hhorizon hepisodes
      hdelta hdeltaOne

end FoundationAndGeneratedChain

section ConcreteTwoStateTwoAction

local instance : MeasurableSpace (Fin 2) := ⊤

noncomputable def twoStateTwoActionMDP : MDP (Fin 2) (Fin 2) where
  horizon := 2
  transition := Kernel.deterministic (fun pair => pair.2) (measurable_of_finite _)
  transition_isMarkov := by infer_instance
  reward := fun state action => if state = action then 1 else 0
  measurable_reward := measurable_of_finite _

lemma twoStateTwoActionMDP_horizon_pos : 0 < twoStateTwoActionMDP.horizon := by
  norm_num [twoStateTwoActionMDP]

lemma twoStateTwoActionMDP_reward_nonneg :
    ∀ state action, 0 <= twoStateTwoActionMDP.reward state action := by
  intro state action
  simp only [twoStateTwoActionMDP]
  split_ifs <;> norm_num

lemma twoStateTwoActionMDP_reward_le_one :
    ∀ state action, twoStateTwoActionMDP.reward state action <= 1 := by
  intro state action
  simp only [twoStateTwoActionMDP]
  split_ifs <;> norm_num

noncomputable def twoStateInitialLaw : Measure (Fin 2) := Measure.dirac 0

noncomputable instance : IsProbabilityMeasure twoStateInitialLaw := by
  dsimp [twoStateInitialLaw]
  infer_instance

/-- Concrete nondegenerate high-probability terminal: `S=A=H=K=2` and
`delta=1/2`. -/
example :
    let source := recurrentSource twoStateTwoActionMDP twoStateInitialLaw
      0 2 (1 / 2)
    source.trajectoryMeasure
        {trajectory |
          canonicalRegretBound (State := Fin 2) (Action := Fin 2)
              twoStateTwoActionMDP 2 (1 / 2) <
            cumulativeEpisodePseudoRegret source 0 2 trajectory} <=
      ENNReal.ofReal (1 / 2) := by
  exact recurrentSource_trajectoryMeasure_cumulativeEpisodePseudoRegret_gt_canonicalRegretBound_le
    twoStateTwoActionMDP twoStateInitialLaw 0 2 (1 / 2)
      twoStateTwoActionMDP_horizon_pos (by norm_num) (by norm_num) (by norm_num)
      twoStateTwoActionMDP_reward_nonneg twoStateTwoActionMDP_reward_le_one

/-- The matching concrete expected theorem retains the failure charge
`2 * 2 * (1/2)`. -/
example :
    let source := recurrentSource twoStateTwoActionMDP twoStateInitialLaw
      0 2 (1 / 2)
    ∫ trajectory,
        cumulativeEpisodePseudoRegret source 0 2 trajectory
          ∂source.trajectoryMeasure <=
      canonicalRegretBound (State := Fin 2) (Action := Fin 2)
          twoStateTwoActionMDP 2 (1 / 2) +
        (2 : Real) * twoStateTwoActionMDP.horizon * (1 / 2) := by
  exact integral_cumulativeEpisodePseudoRegret_recurrentSource_le_canonicalRegretBound_add_failure
    twoStateTwoActionMDP twoStateInitialLaw 0 2 (1 / 2)
      twoStateTwoActionMDP_horizon_pos (by norm_num) (by norm_num) (by norm_num)
      twoStateTwoActionMDP_reward_nonneg twoStateTwoActionMDP_reward_le_one

end ConcreteTwoStateTwoAction

#print axioms FiniteHorizonRL.MDP.optimalValueAt_dominates_and_is_attained
#print axioms FiniteHorizonRL.MarkovPolicy.expectedRegret_eq_occupancyGapRemaining
#print axioms FiniteHorizonRL.sum_adaptiveCumulativeAggregateTransitionCountAt_eq_visitCountAt
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.clippedQRemaining_of_aggregateVisitCount_pos
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.recurrentSource_trajectoryMeasure_simultaneousTransitionFailureEvent_le_fifth
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource.recurrentQTableOfTrajectory_dominatesOptimal
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource.recurrentSource_generatedSuccessorPseudoRegret_le_charge_add_innovation
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.totalGeneratedPairCharge_le_explicit
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.recurrentSource_trajectoryMeasure_bellmanInnovation_sum_ge_threshold_le_fifth
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.recurrentSource_trajectoryMeasure_cumulativeEpisodePseudoRegret_gt_canonicalRegretBound_le
#print axioms FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI.integral_cumulativeEpisodePseudoRegret_recurrentSource_le_canonicalRegretBound_add_failure

end BanditRLProof.BookMapChapterNineCanary
