import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIAdaptiveBellmanMartingale

/-! Pathwise recurrent UCBVI-CH episode-regret decomposition. -/

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

namespace AdaptiveCumulativeHoeffdingUCBVI

/-- Previous Q table for successor episode `n+1`. -/
noncomputable def successorPreviousQ
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) : QTable mdp :=
  recurrentQTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta) n
    (fun i => (trajectory i).transitionCountSummary)

/-- Exact pooled summary available before successor episode `n+1`. -/
def successorSummary
    {mdp : MDP State Action}
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    TransitionCountSummary mdp :=
  (adaptiveCumulativeEmpiricalModelStateAt trajectory n).1

/-- Greedy recurrent table actually used by successor episode `n+1`. -/
noncomputable def successorPolicyTable
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    DeterministicMarkovPolicyTable mdp :=
  clippedPolicyTable mdp
    (successorPreviousQ mdp defaultState episodes delta trajectory n)
    (successorSummary trajectory n) defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)

/-- Same-policy continuation gap in the successor episode. -/
noncomputable def successorPolicyGapRemaining
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n remaining : Nat)
    (hremaining : remaining <= mdp.horizon) (state : State) : Real :=
  clippedPolicyGapRemaining
    (successorPreviousQ mdp defaultState episodes delta trajectory n)
    (successorSummary trajectory n) defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)
    remaining hremaining state

/-- Per-stage deterministic charge.  A zero previous count is paid by `H`;
positive counts pay the `9HL/sqrt N` bonus/projection term plus the explicit
`66 S H^2 L/N` Bernstein correction. -/
noncomputable def successorLocalCharge
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) : Real :=
  let stage := mdp.decisionStageRemaining remaining hremaining
  let action := successorPolicyTable mdp defaultState episodes delta trajectory n
    stage state
  let count := (successorSummary trajectory n).aggregateVisitCount state action
  if count = 0 then
    (mdp.horizon : Real)
  else
    min (mdp.horizon : Real)
      (9 * (mdp.horizon : Real) *
          logFactor (State := State) (Action := Action) mdp episodes delta /
            Real.sqrt count +
        66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
          logFactor (State := State) (Action := Action) mdp episodes delta /
            count)

theorem successorPolicyGapRemaining_mem_Icc
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hrewardOne : forall state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉
      AdaptiveEpisodeBatchSource.simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (n : Nat) (hn : n + 1 <= episodes)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) (state : State) :
    successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
      remaining hremaining state ∈ Set.Icc (0 : Real) mdp.horizon := by
  let previousQ := successorPreviousQ mdp defaultState episodes delta trajectory n
  let summary := successorSummary trajectory n
  let bonusScale := scale (State := State) (Action := Action) mdp episodes delta
  let table := clippedPolicyTable mdp previousQ summary defaultState bonusScale
  let policy := table.toMarkovPolicy
  let upper := clippedValueRemaining previousQ summary defaultState bonusScale
    remaining hremaining state
  have hsummary : summary = cumulativeSummaryOfSequence
      (fun i : Fin (n + 1) => (trajectory i).transitionCountSummary) := by
    symm
    simpa [summary] using
      cumulativeSummaryOfSequence_prefixTransitionSummaries_eq trajectory n
  have hdomFold :=
    AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource.recurrentQTableOfTrajectory_dominatesOptimal
      source hhorizon hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne
        htrajectory defaultState (n + 1) hn
  have hdom : QDominatesOptimal mdp
      (clippedQTable mdp previousQ summary defaultState bonusScale) := by
    simpa [previousQ, summary, bonusScale, hsummary,
      recurrentQTableOfSummaries] using hdomFold
  have hoptLe : mdp.optimalValueAt (mdp.horizon - remaining)
        (Nat.sub_le _ _) state <= upper :=
    optimalValueAt_le_clippedValueRemaining previousQ summary defaultState
      bonusScale hdom remaining hremaining state
  have hpolicyLe : policy.valueRemaining remaining hremaining state <=
      mdp.optimalValueAt (mdp.horizon - remaining) (Nat.sub_le _ _) state := by
    have h := policy.valueAt_le_optimalValueAt (mdp.horizon - remaining)
      (Nat.sub_le _ _) state
    unfold MarkovPolicy.valueAt at h
    have hinverse : mdp.horizon - (mdp.horizon - remaining) = remaining := by omega
    rw [congrFun (policy.valueRemaining_eq_of_eq (Nat.sub_le _ _) hremaining
      hinverse) state] at h
    exact h
  have hupperLe : upper <= (mdp.horizon : Real) :=
    clippedValueRemaining_le_horizon previousQ summary defaultState bonusScale
      remaining hremaining state
  have hpolicyNonneg : 0 <= policy.valueRemaining remaining hremaining state :=
    policy.valueRemaining_nonneg_of_reward_nonneg hrewardNonneg remaining
      hremaining state
  change upper - policy.valueRemaining remaining hremaining state ∈
    Set.Icc (0 : Real) mdp.horizon
  constructor <;> linarith

theorem successorLocalCharge_nonneg
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    0 <= successorLocalCharge mdp defaultState episodes delta trajectory n
      remaining hremaining state := by
  simp only [successorLocalCharge]
  split_ifs
  · positivity
  · have hlog := logFactor_nonneg (State := State) (Action := Action)
      mdp episodes delta
    exact le_min (Nat.cast_nonneg _) (add_nonneg (by positivity) (by positivity))

/-- Normalized weight at the start of a subproblem with `remaining` decisions. -/
noncomputable def normalizedBellmanRemainingWeight
    (mdp : MDP State Action) (remaining : Nat) : Real :=
  (31 / 32 : Real) * bellmanInflation mdp ^ (mdp.horizon - remaining)

theorem normalizedBellmanRemainingWeight_zero
    (mdp : MDP State Action) :
    normalizedBellmanRemainingWeight mdp mdp.horizon = 31 / 32 := by
  simp [normalizedBellmanRemainingWeight]

theorem normalizedBellmanRemainingWeight_succ_eq_chargeWeight
    (mdp : MDP State Action) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) :
    normalizedBellmanRemainingWeight mdp (remaining + 1) =
      normalizedBellmanChargeWeight mdp
        (mdp.decisionStageRemaining remaining hremaining) := by
  unfold normalizedBellmanRemainingWeight normalizedBellmanChargeWeight
  rfl

theorem normalizedBellmanRemainingWeight_eq_stageWeight
    (mdp : MDP State Action) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) :
    normalizedBellmanRemainingWeight mdp remaining =
      normalizedBellmanWeight mdp
        (mdp.decisionStageRemaining remaining hremaining) := by
  have hexp : mdp.horizon - remaining =
      (mdp.decisionStageRemaining remaining hremaining).val + 1 := by
    change mdp.horizon - remaining = mdp.horizon - (remaining + 1) + 1
    omega
  unfold normalizedBellmanRemainingWeight normalizedBellmanWeight
  rw [hexp]

/-- Weighted local charges along the state sequence reconstructed recursively
from one successor batch. -/
noncomputable def successorWeightedChargeFrom
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State ->
      StepTrace Action State remaining -> Real
  | 0, _, _, _ => 0
  | remaining + 1, hremaining, state, trace =>
      let stage := mdp.decisionStageRemaining remaining hremaining
      normalizedBellmanChargeWeight mdp stage *
          successorLocalCharge mdp defaultState episodes delta trajectory n
            remaining hremaining state +
        successorWeightedChargeFrom mdp defaultState episodes delta trajectory n
          remaining (by omega) (trace 0).2 (Fin.tail trace)

/-- Full successor-episode charge on the canonical state reconstruction. -/
noncomputable def successorCanonicalWeightedCharge
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) : Real :=
  successorWeightedChargeFrom mdp defaultState episodes delta trajectory n
    mdp.horizon le_rfl
    ((trajectory (n + 1)).reconstructedInitialState defaultState)
    ((trajectory (n + 1)).reconstructedStepTrace)

/-- Chronological weighted charge of one successor episode. -/
noncomputable def successorWeightedChargeSum
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
  (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) : Real :=
  ∑ stage : Fin mdp.horizon,
    normalizedBellmanChargeWeight mdp stage *
      successorLocalCharge mdp defaultState episodes delta trajectory n
        (mdp.horizon - (stage.val + 1)) (by omega)
        (trajectory (n + 1) 0 stage).state

theorem successorWeightedChargeSum_nonneg
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    0 <= successorWeightedChargeSum mdp defaultState episodes delta trajectory n := by
  exact Finset.sum_nonneg fun stage _ => mul_nonneg
    (normalizedBellmanChargeWeight_mem_Icc mdp
      (by have := stage.isLt; omega) stage).1
    (successorLocalCharge_nonneg mdp defaultState episodes delta trajectory n
      (mdp.horizon - (stage.val + 1)) (by omega)
      (trajectory (n + 1) 0 stage).state)

/-- Weighted state-gap transported along one generated successor batch. -/
noncomputable def successorWeightedVisitedGap
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat)
    (stage : Fin mdp.horizon) : Real :=
  normalizedBellmanWeight mdp stage *
    successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
      (mdp.horizon - stage.val) (by omega)
      (trajectory (n + 1) 0 stage).state

namespace AdaptiveEpisodeBatchSource

/-- The good same-source transition event discharges the complete local
inflated Bellman recursion at every successor episode and state. -/
theorem successorPolicyGapRemaining_le_inflation_mul_transition_add_charge
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hrewardOne : forall state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (n : Nat) (hn : n + 1 < episodes)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
        (remaining + 1) hremaining state <=
      bellmanInflation mdp *
        mdp.transitionValue
          (successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
            remaining (by omega))
          state
          (successorPolicyTable mdp defaultState episodes delta trajectory n
            (mdp.decisionStageRemaining remaining hremaining) state) +
        successorLocalCharge mdp defaultState episodes delta trajectory n
          remaining hremaining state := by
  let previousQ := successorPreviousQ mdp defaultState episodes delta trajectory n
  let summary := successorSummary trajectory n
  let bonusScale := scale (State := State) (Action := Action) mdp episodes delta
  let stage := mdp.decisionStageRemaining remaining hremaining
  let table := clippedPolicyTable mdp previousQ summary defaultState bonusScale
  let selected := table stage state
  let gap := clippedPolicyGapRemaining previousQ summary defaultState bonusScale
    remaining (by omega)
  let count := summary.aggregateVisitCount state selected
  have hround : n < episodes := by omega
  let round : Fin episodes := ⟨n, hround⟩
  have hsummary : summary =
      (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1 := by rfl
  have hdomFold :=
    AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource.recurrentQTableOfTrajectory_dominatesOptimal
      source
    hhorizon hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne htrajectory
      defaultState (n + 1) (by omega)
  have hdom : QDominatesOptimal mdp
      (clippedQTable mdp previousQ summary defaultState bonusScale) := by
    have hsum : cumulativeSummaryOfSequence
        (fun i : Fin (n + 1) => (trajectory i).transitionCountSummary) = summary := by
      simpa [summary] using
        cumulativeSummaryOfSequence_prefixTransitionSummaries_eq trajectory n
    simpa [previousQ, summary, bonusScale, hsum,
      recurrentQTableOfSummaries] using hdomFold
  change clippedPolicyGapRemaining previousQ summary defaultState bonusScale
        (remaining + 1) hremaining state <=
      bellmanInflation mdp * mdp.transitionValue gap state selected +
        (if count = 0 then (mdp.horizon : Real) else
          min (mdp.horizon : Real) (9 * (mdp.horizon : Real) *
              logFactor (State := State) (Action := Action) mdp episodes delta /
                Real.sqrt count +
            66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
              logFactor (State := State) (Action := Action) mdp episodes delta /
                count))
  by_cases hcount : count = 0
  · have hgapBound := successorPolicyGapRemaining_mem_Icc source hhorizon
      hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne htrajectory
      defaultState n (by omega) (remaining + 1) hremaining state
    have hnextNonneg (nextState : State) : 0 <= gap nextState := by
      simpa [gap, previousQ, summary, bonusScale] using
        (successorPolicyGapRemaining_mem_Icc source hhorizon hepisodes hdelta
          hdelta_le_one hrewardNonneg hrewardOne htrajectory defaultState n
          (by omega) remaining (by omega) nextState).1
    have htransition : 0 <= mdp.transitionValue gap state selected := by
      unfold MDP.transitionValue
      exact integral_nonneg hnextNonneg
    rw [if_pos hcount]
    have hgapUpper : clippedPolicyGapRemaining previousQ summary defaultState
        bonusScale (remaining + 1) hremaining state <= (mdp.horizon : Real) := by
      simpa [successorPolicyGapRemaining, previousQ, summary, bonusScale] using
        hgapBound.2
    have hinflation : 0 <= bellmanInflation mdp := by
      linarith [bellmanInflation_one_le mdp]
    have hmul := mul_nonneg hinflation htransition
    linarith
  · have hcountPos : 0 < count := Nat.pos_of_ne_zero hcount
    have hcountLeRound := adaptiveCumulativeAggregateVisitCountAt_le
      trajectory n state selected
    have hcountLe : count <= episodes * mdp.horizon := by
      exact hcountLeRound.trans (Nat.mul_le_mul_right mdp.horizon (by omega))
    let countIndex : Fin (episodes * mdp.horizon) := ⟨count - 1, by omega⟩
    have hactual : adaptiveCumulativeAggregateVisitCountAt trajectory round state
        (clippedPolicyTable mdp previousQ
          (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
          defaultState bonusScale stage state) = countIndex + 1 := by
      change count = (count - 1) + 1
      omega
    have hlocal :=
      AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource.selectedPolicyGap_le_of_actual_count
      source htrajectory
      defaultState round previousQ remaining hremaining state countIndex hactual
      hdom hhorizon hrewardNonneg
    have hhorizonReal : 0 < (mdp.horizon : Real) := by exact_mod_cast hhorizon
    have htransitionNonneg : 0 <= mdp.transitionValue gap state selected := by
      have hnext (nextState : State) : 0 <= gap nextState := by
        simpa [gap, previousQ, summary, bonusScale] using
          (successorPolicyGapRemaining_mem_Icc source hhorizon hepisodes hdelta
            hdelta_le_one hrewardNonneg hrewardOne htrajectory defaultState n
            (by omega) remaining (by omega) nextState).1
      unfold MDP.transitionValue
      exact integral_nonneg hnext
    have hinflate : mdp.transitionValue gap state selected +
          mdp.transitionValue gap state selected / (32 * mdp.horizon) =
        bellmanInflation mdp * mdp.transitionValue gap state selected := by
      unfold bellmanInflation
      field_simp
    rw [if_neg hcount]
    have hExpr : clippedPolicyGapRemaining previousQ summary defaultState
        bonusScale (remaining + 1) hremaining state <=
      bellmanInflation mdp * mdp.transitionValue gap state selected +
        (9 * (mdp.horizon : Real) *
              logFactor (State := State) (Action := Action) mdp episodes delta /
                Real.sqrt count +
            66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
              logFactor (State := State) (Action := Action) mdp episodes delta /
                count) := by
      rw [← hinflate]
      convert hlocal using 1 <;>
        simp [round, previousQ, summary, successorSummary, bonusScale, table,
          stage, selected, gap, countIndex, Nat.sub_add_cancel hcountPos] <;> ring
    have hgapBound := successorPolicyGapRemaining_mem_Icc source hhorizon
      hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne htrajectory
      defaultState n (by omega) (remaining + 1) hremaining state
    have hinflation : 0 <= bellmanInflation mdp := by
      linarith [bellmanInflation_one_le mdp]
    have hH : clippedPolicyGapRemaining previousQ summary defaultState
        bonusScale (remaining + 1) hremaining state <=
      bellmanInflation mdp * mdp.transitionValue gap state selected +
        (mdp.horizon : Real) := by
      have hgapUpper : clippedPolicyGapRemaining previousQ summary defaultState
          bonusScale (remaining + 1) hremaining state <= (mdp.horizon : Real) := by
        simpa [successorPolicyGapRemaining, previousQ, summary, bonusScale] using
          hgapBound.2
      have hmul := mul_nonneg hinflation htransitionNonneg
      linarith
    by_cases hsmall : (mdp.horizon : Real) <=
        9 * (mdp.horizon : Real) *
              logFactor (State := State) (Action := Action) mdp episodes delta /
                Real.sqrt count +
            66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
              logFactor (State := State) (Action := Action) mdp episodes delta /
                count
    · rw [min_eq_left hsmall]
      exact hH
    · rw [min_eq_right (le_of_not_ge hsmall)]
      exact hExpr

/-- On the joint confidence event, the globally clipped martingale feature is
exactly the normalized recurrent policy gap. -/
theorem clippedSuccessorGapFeatureOfSummaries_eq_weight_mul_gap
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hrewardOne : forall state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (n : Nat) (hn : n + 1 <= episodes)
    (stage : Fin mdp.horizon) (state : State) :
    clippedSuccessorGapFeatureOfSummaries mdp defaultState episodes delta n
        (fun i => (trajectory i).transitionCountSummary) stage state =
      normalizedBellmanWeight mdp stage *
        successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
          (mdp.horizon - (stage.val + 1)) (by omega) state := by
  have hgap := successorPolicyGapRemaining_mem_Icc source hhorizon hepisodes
    hdelta hdelta_le_one hrewardNonneg hrewardOne htrajectory defaultState n hn
    (mdp.horizon - (stage.val + 1)) (by omega) state
  unfold clippedSuccessorGapFeatureOfSummaries
  have hsummary : cumulativeSummaryOfSequence
      (fun i : Fin (n + 1) => (trajectory i).transitionCountSummary) =
      successorSummary trajectory n := by
    simpa [successorSummary] using
      cumulativeSummaryOfSequence_prefixTransitionSummaries_eq trajectory n
  rw [hsummary]
  have hmin : min
      (successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
        (mdp.horizon - (stage.val + 1)) (by omega) state)
      (mdp.horizon : Real) =
      successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
        (mdp.horizon - (stage.val + 1)) (by omega) state :=
    min_eq_left hgap.2
  have hmax : max 0
      (successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
        (mdp.horizon - (stage.val + 1)) (by omega) state) =
      successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
        (mdp.horizon - (stage.val + 1)) (by omega) state :=
    max_eq_right hgap.1
  dsimp only [successorPolicyGapRemaining, successorPreviousQ,
    successorSummary] at hmin hmax ⊢
  simp only [Fin.coe_castSucc] at ⊢
  rw [hmin, hmax]

/-- Exact weighted Bellman telescope for one successor episode.  The charge,
policy table, recursively reconstructed state path, and martingale innovation
are all the same objects used by the recurrent generated source. -/
theorem normalizedGap_le_weightedChargeFrom_add_deterministicInnovation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hrewardOne : forall state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (n : Nat) (hn : n + 1 < episodes) :
    forall (remaining : Nat) (hremaining : remaining <= mdp.horizon)
      (state : State) (trace : StepTrace Action State remaining),
      normalizedBellmanRemainingWeight mdp remaining *
          successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
            remaining hremaining state <=
        successorWeightedChargeFrom mdp defaultState episodes delta trajectory n
            remaining hremaining state trace +
          mdp.sampledCumulativeDeterministicGapInnovationFrom
            (successorPolicyTable mdp defaultState episodes delta trajectory n)
            (clippedSuccessorGapFeatureOfSummaries mdp defaultState episodes delta n
              (fun i => (trajectory i).transitionCountSummary))
            remaining hremaining state trace := by
  intro remaining
  induction remaining with
  | zero =>
      intro hremaining state trace
      simp [normalizedBellmanRemainingWeight, successorPolicyGapRemaining,
        clippedPolicyGapRemaining, clippedValueRemaining,
        MarkovPolicy.valueRemaining, successorWeightedChargeFrom,
        MDP.sampledCumulativeDeterministicGapInnovationFrom]
  | succ remaining ih =>
      intro hremaining state trace
      let stage := mdp.decisionStageRemaining remaining hremaining
      let table := successorPolicyTable mdp defaultState episodes delta trajectory n
      let gap := successorPolicyGapRemaining mdp defaultState episodes delta
        trajectory n remaining (by omega)
      let feature := clippedSuccessorGapFeatureOfSummaries mdp defaultState
        episodes delta n (fun i => (trajectory i).transitionCountSummary)
      let charge := successorLocalCharge mdp defaultState episodes delta trajectory n
        remaining hremaining state
      let weight := normalizedBellmanChargeWeight mdp stage
      have hlocal :=
        successorPolicyGapRemaining_le_inflation_mul_transition_add_charge
          source hhorizon hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne
          htrajectory defaultState n hn remaining hremaining state
      have hweightNonneg : 0 <= weight :=
        (normalizedBellmanChargeWeight_mem_Icc mdp hhorizon stage).1
      have hmul := mul_le_mul_of_nonneg_left hlocal hweightNonneg
      have hfeature (nextState : State) :
          feature stage nextState =
            normalizedBellmanWeight mdp stage * gap nextState := by
        have hrem : mdp.horizon - (stage.val + 1) = remaining := by
          simp [stage, MDP.decisionStageRemaining]
          omega
        have h := clippedSuccessorGapFeatureOfSummaries_eq_weight_mul_gap source
            hhorizon hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne
            htrajectory defaultState n (by omega) stage nextState
        simp only [hrem] at h
        simpa [feature, gap, stage] using h
      have htransition :
          mdp.transitionValue (feature stage) state (table stage state) =
            normalizedBellmanWeight mdp stage *
              mdp.transitionValue gap state (table stage state) := by
        unfold MDP.transitionValue
        simp_rw [hfeature]
        rw [integral_const_mul]
      have htail := ih (by omega) (trace 0).2 (Fin.tail trace)
      have htailWeight : normalizedBellmanRemainingWeight mdp remaining =
          normalizedBellmanWeight mdp stage := by
        simpa [stage] using
          normalizedBellmanRemainingWeight_eq_stageWeight mdp remaining hremaining
      have htail' : feature stage (trace 0).2 <=
          successorWeightedChargeFrom mdp defaultState episodes delta trajectory n
              remaining (by omega) (trace 0).2 (Fin.tail trace) +
            mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
              remaining (by omega) (trace 0).2 (Fin.tail trace) := by
        rw [hfeature, ← htailWeight]
        simpa [table, feature] using htail
      have hheadWeight : normalizedBellmanRemainingWeight mdp (remaining + 1) =
          weight := by
        simpa [weight, stage] using
          normalizedBellmanRemainingWeight_succ_eq_chargeWeight mdp remaining hremaining
      have hscale : weight * bellmanInflation mdp =
          normalizedBellmanWeight mdp stage := by
        simpa [weight] using
          normalizedBellmanChargeWeight_mul_inflation mdp stage
      rw [mul_add, ← mul_assoc, hscale] at hmul
      have hfinal : weight *
          successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
            (remaining + 1) hremaining state <=
        (weight * charge +
            successorWeightedChargeFrom mdp defaultState episodes delta trajectory n
              remaining (by omega) (trace 0).2 (Fin.tail trace)) +
          (mdp.transitionValue (feature stage) state (table stage state) -
            feature stage (trace 0).2 +
            mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
              remaining (by omega) (trace 0).2 (Fin.tail trace)) := by
        rw [htransition]
        dsimp only [weight, charge, table, gap, stage] at hmul
        dsimp only [table, feature] at htail'
        dsimp only [weight, charge, table, gap, stage, feature]
        linarith
      simpa only [successorWeightedChargeFrom,
        MDP.sampledCumulativeDeterministicGapInnovationFrom, hheadWeight,
        stage, table, feature, charge, weight] using hfinal

/-- The full-horizon successor policy gap is bounded by the globally capped
canonical charge plus the exact successor Bellman innovation. -/
theorem successorPolicyGapRemaining_le_cap_mul_charge_add_innovation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hrewardOne : forall state action, mdp.reward state action <= 1)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent source episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (defaultState : State) (n : Nat) (hn : n + 1 < episodes) :
    successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
        mdp.horizon le_rfl
        ((trajectory (n + 1)).reconstructedInitialState defaultState) <=
      bellmanWeightCap *
        (successorCanonicalWeightedCharge mdp defaultState episodes delta
            trajectory n +
          mdp.sampledCumulativeDeterministicGapInnovationFrom
            (successorPolicyTable mdp defaultState episodes delta trajectory n)
            (clippedSuccessorGapFeatureOfSummaries mdp defaultState episodes delta n
              (fun i => (trajectory i).transitionCountSummary))
            mdp.horizon le_rfl
            ((trajectory (n + 1)).reconstructedInitialState defaultState)
            ((trajectory (n + 1)).reconstructedStepTrace)) := by
  have h := normalizedGap_le_weightedChargeFrom_add_deterministicInnovation
    source hhorizon hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne
    htrajectory defaultState n hn mdp.horizon le_rfl
    ((trajectory (n + 1)).reconstructedInitialState defaultState)
    ((trajectory (n + 1)).reconstructedStepTrace)
  have hcapNonneg : 0 <= bellmanWeightCap := by
    norm_num [bellmanWeightCap]
  have hmul := mul_le_mul_of_nonneg_left h hcapNonneg
  have hcancel : bellmanWeightCap * (31 / 32 : Real) = 1 := by
    norm_num [bellmanWeightCap]
  rw [normalizedBellmanRemainingWeight_zero, ← mul_assoc, hcancel,
    one_mul] at hmul
  simpa [successorCanonicalWeightedCharge] using hmul

/-- Optimism converts the generated successor episode's policy-value
pseudo-regret into the same recurrent policy gap used by the telescope. -/
theorem recurrentSource_generatedEpisodePseudoRegret_le_successorPolicyGapRemaining
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hrewardOne : forall state action, mdp.reward state action <= 1)
    (defaultState : State)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent
      (recurrentSource mdp initialState defaultState episodes delta) episodes
      (logFactor (State := State) (Action := Action) mdp episodes delta))
    (n : Nat) (hn : n + 1 < episodes) :
    generatedEpisodePseudoRegret
        (recurrentSource mdp initialState defaultState episodes delta)
        defaultState trajectory (n + 1) <=
      successorPolicyGapRemaining mdp defaultState episodes delta trajectory n
        mdp.horizon le_rfl
        ((trajectory (n + 1)).reconstructedInitialState defaultState) := by
  let source := recurrentSource mdp initialState defaultState episodes delta
  let previousQ := successorPreviousQ mdp defaultState episodes delta trajectory n
  let summary := successorSummary trajectory n
  let bonusScale := scale (State := State) (Action := Action) mdp episodes delta
  let table := successorPolicyTable mdp defaultState episodes delta trajectory n
  let state := (trajectory (n + 1)).reconstructedInitialState defaultState
  have hsummary : summary = cumulativeSummaryOfSequence
      (fun i : Fin (n + 1) => (trajectory i).transitionCountSummary) := by
    symm
    simpa [summary] using
      cumulativeSummaryOfSequence_prefixTransitionSummaries_eq trajectory n
  have hdomFold := recurrentQTableOfTrajectory_dominatesOptimal source hhorizon
    hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne
      (by simpa [source] using htrajectory) defaultState (n + 1) (by omega)
  have hdom : QDominatesOptimal mdp
      (clippedQTable mdp previousQ summary defaultState bonusScale) := by
    simpa [previousQ, summary, bonusScale, hsummary,
      recurrentQTableOfSummaries] using hdomFold
  have hoptLe : mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state <=
      clippedValueRemaining previousQ summary defaultState bonusScale
        mdp.horizon le_rfl state := by
    simpa using optimalValueAt_le_clippedValueRemaining previousQ summary
      defaultState bonusScale hdom mdp.horizon le_rfl state
  have htable : generatedPolicyTable mdp defaultState episodes delta trajectory
      (n + 1) = table := by
    funext stage currentState
    unfold generatedPolicyTable table successorPolicyTable
    simp only [recurrentPolicyTableOfSummaries, successorPreviousQ,
      successorSummary]
    rw [recurrentQTableOfSummaries]
    rw [← hsummary]
    rfl
  have hpolicy : source.policyAt trajectory (n + 1) = table.toMarkovPolicy := by
    rw [recurrentSource_policyAt_eq_generatedPolicyTable]
    rw [htable]
  have hstate : generatedEpisodeInitialState mdp defaultState
      (trajectory (n + 1)) = state := by
    simp [generatedEpisodeInitialState, state, EpisodeBatch.reconstructedInitialState,
      hhorizon]
  unfold generatedEpisodePseudoRegret
  rw [hstate, hpolicy]
  unfold MarkovPolicy.valueAt successorPolicyGapRemaining clippedPolicyGapRemaining
  change mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
      table.toMarkovPolicy.valueRemaining mdp.horizon le_rfl state <=
    clippedValueRemaining previousQ summary defaultState bonusScale mdp.horizon
        le_rfl state -
      table.toMarkovPolicy.valueRemaining mdp.horizon le_rfl state
  exact sub_le_sub_right hoptLe _

/-- The named adaptive martingale process is definitionally the direct
canonical innovation used in the successor telescope. -/
theorem recurrentBellmanInnovationProcess_succ_eq_canonical
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    recurrentBellmanInnovationProcess mdp defaultState episodes delta (n + 1)
        trajectory =
      mdp.sampledCumulativeDeterministicGapInnovationFrom
        (successorPolicyTable mdp defaultState episodes delta trajectory n)
        (clippedSuccessorGapFeatureOfSummaries mdp defaultState episodes delta n
          (fun i => (trajectory i).transitionCountSummary))
        mdp.horizon le_rfl
        ((trajectory (n + 1)).reconstructedInitialState defaultState)
        ((trajectory (n + 1)).reconstructedStepTrace) := by
  rfl

/-- End-to-end good-event decomposition for one generated successor episode. -/
theorem recurrentSource_generatedSuccessorPseudoRegret_le_charge_add_innovation
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : forall state action, 0 <= mdp.reward state action)
    (hrewardOne : forall state action, mdp.reward state action <= 1)
    (defaultState : State)
    (htrajectory : trajectory ∉ simultaneousTransitionFailureEvent
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
  have hreg :=
    recurrentSource_generatedEpisodePseudoRegret_le_successorPolicyGapRemaining
      initialState hhorizon hepisodes hdelta hdelta_le_one hrewardNonneg
      hrewardOne defaultState htrajectory n hn
  have hgap := successorPolicyGapRemaining_le_cap_mul_charge_add_innovation
    (recurrentSource mdp initialState defaultState episodes delta)
    hhorizon hepisodes hdelta hdelta_le_one hrewardNonneg hrewardOne htrajectory
    defaultState n hn
  rw [← recurrentBellmanInnovationProcess_succ_eq_canonical mdp defaultState
    episodes delta trajectory n] at hgap
  exact hreg.trans hgap

end AdaptiveEpisodeBatchSource

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
