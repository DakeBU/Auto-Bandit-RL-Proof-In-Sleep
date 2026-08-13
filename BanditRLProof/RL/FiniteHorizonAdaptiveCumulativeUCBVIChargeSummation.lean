import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVICounting
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 1000000

/-! Canonical generated-record alignment and UCBVI-CH charge summation. -/

open MeasureTheory
open scoped BigOperators

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveCumulativeHoeffdingUCBVI

/-- Aggregate visits contributed by one actual generated batch. -/
def generatedBatchAggregateVisitIncrement
    {mdp : MDP State Action} (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) (episode : Nat) : Nat :=
  (trajectory episode).transitionCountSummary.aggregateVisitCount state action

theorem batchedPrefixCount_generatedBatchAggregateVisitIncrement
    {mdp : MDP State Action} (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) (round : Nat) :
    batchedPrefixCount
        (generatedBatchAggregateVisitIncrement trajectory state action) (round + 1) =
      adaptiveCumulativeAggregateVisitCountAt trajectory round state action := by
  rw [adaptiveCumulativeAggregateVisitCountAt_eq_sum]
  unfold batchedPrefixCount
  rw [← Fin.sum_univ_eq_sum_range]
  simp [generatedBatchAggregateVisitIncrement,
    TransitionCountSummary.aggregateVisitCount,
    EpisodeBatch.transitionCountSummary_visitCount]

theorem generatedBatchAggregateVisitIncrement_le_horizon
    {mdp : MDP State Action} (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) (episode : Nat) :
    generatedBatchAggregateVisitIncrement trajectory state action episode <=
      mdp.horizon :=
  (trajectory episode).aggregateVisitCount_le_horizon state action

/-- Every stored state/action record is aligned with its reconstructed full
trajectory and with the deterministic recurrent choice.  This is the exact
portion of mapped-batch identity consumed by the regret ledger. -/
def SuccessorBatchAligned
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) : Prop :=
  let batch := trajectory (n + 1)
  let reconstructed : State × StepTrace Action State mdp.horizon :=
    (batch.reconstructedInitialState defaultState, batch.reconstructedStepTrace)
  forall stage : Fin mdp.horizon,
    (batch 0 stage).state = mdp.trajectoryStateAt reconstructed stage ∧
      (batch 0 stage).action =
        successorPolicyTable mdp defaultState episodes delta trajectory n stage
          (mdp.trajectoryStateAt reconstructed stage)

/-- On an aligned successor batch, each canonical recursively selected
state/action pair is exactly the corresponding stored empirical record. -/
theorem successorBatchAligned_step
    {mdp : MDP State Action} {defaultState : State}
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1} {n : Nat}
    (haligned : SuccessorBatchAligned mdp defaultState episodes delta trajectory n)
    (stage : Fin mdp.horizon) :
    let batch := trajectory (n + 1)
    let reconstructed : State × StepTrace Action State mdp.horizon :=
      (batch.reconstructedInitialState defaultState, batch.reconstructedStepTrace)
    (batch 0 stage).state = mdp.trajectoryStateAt reconstructed stage ∧
      (batch 0 stage).action =
        successorPolicyTable mdp defaultState episodes delta trajectory n stage
          (mdp.trajectoryStateAt reconstructed stage) := by
  dsimp only
  let batch := trajectory (n + 1)
  let reconstructed : State × StepTrace Action State mdp.horizon :=
    (batch.reconstructedInitialState defaultState, batch.reconstructedStepTrace)
  exact haligned stage

/-- Number of stored visits to one pair is the sum of its stage indicators. -/
theorem generatedBatchAggregateVisitIncrement_eq_indicatorSum
    {mdp : MDP State Action} (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) (episode : Nat) :
    generatedBatchAggregateVisitIncrement trajectory state action episode =
      ∑ stage : Fin mdp.horizon,
        if (trajectory episode 0 stage).state = state ∧
          (trajectory episode 0 stage).action = action then 1 else 0 := by
  rw [show generatedBatchAggregateVisitIncrement trajectory state action episode =
      ∑ stage : Fin mdp.horizon,
        (trajectory episode).visitCount stage state action by
    unfold generatedBatchAggregateVisitIncrement
    unfold TransitionCountSummary.aggregateVisitCount
    apply Finset.sum_congr rfl
    intro stage _
    exact (trajectory episode).transitionCountSummary_visitCount stage state action]
  apply Finset.sum_congr rfl
  intro stage _
  unfold EpisodeBatch.visitCount
  simp only [Fin.sum_univ_one]

/-- The sum of all pair increments in one one-trajectory batch is exactly H. -/
theorem sum_generatedBatchAggregateVisitIncrement_eq_horizon
    {mdp : MDP State Action} (trajectory : EpisodeBatchTrajectory mdp 1)
    (episode : Nat) :
    ∑ state : State, ∑ action : Action,
      generatedBatchAggregateVisitIncrement trajectory state action episode =
        mdp.horizon := by
  simp_rw [generatedBatchAggregateVisitIncrement_eq_indicatorSum]
  calc
    (∑ state : State, ∑ action : Action, ∑ stage : Fin mdp.horizon,
        if (trajectory episode 0 stage).state = state ∧
          (trajectory episode 0 stage).action = action then 1 else 0) =
      ∑ state : State, ∑ stage : Fin mdp.horizon, ∑ action : Action,
        if (trajectory episode 0 stage).state = state ∧
          (trajectory episode 0 stage).action = action then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.sum_comm]
    _ =
      ∑ stage : Fin mdp.horizon, ∑ state : State, ∑ action : Action,
        if (trajectory episode 0 stage).state = state ∧
          (trajectory episode 0 stage).action = action then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _stage : Fin mdp.horizon, 1 := by
      apply Finset.sum_congr rfl
      intro stage _
      calc
        (∑ state : State, ∑ action : Action,
            if (trajectory episode 0 stage).state = state ∧
              (trajectory episode 0 stage).action = action then 1 else 0) =
          ∑ state : State,
            if (trajectory episode 0 stage).state = state then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro state _
            by_cases hs : (trajectory episode 0 stage).state = state
            · simp [hs]
            · simp [hs]
        _ = 1 := by simp
    _ = mdp.horizon := by simp

/-- The clipped UCBVI-CH charge assigned to one state-action pair in one
episode, using the literal strict-prefix count of generated batch records. -/
noncomputable def generatedPairLocalCharge
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) (episode : Nat) : Real :=
  let count := batchedPrefixCount
    (generatedBatchAggregateVisitIncrement trajectory state action) episode
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

theorem generatedPairLocalCharge_nonneg
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) (episode : Nat) :
    0 <= generatedPairLocalCharge mdp episodes delta trajectory state action
      episode := by
  simp only [generatedPairLocalCharge]
  split_ifs
  · positivity
  · have hlog := logFactor_nonneg (State := State) (Action := Action)
      mdp episodes delta
    exact le_min (Nat.cast_nonneg _) (add_nonneg (by positivity) (by positivity))

/-- Alignment converts the policy-selected local charge at a recorded stage
to the pair charge indexed by that record's exact state and action. -/
theorem successorLocalCharge_eq_generatedPairLocalCharge_of_aligned
    {mdp : MDP State Action} {defaultState : State}
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1} {n : Nat}
    (haligned : SuccessorBatchAligned mdp defaultState episodes delta trajectory n)
    (stage : Fin mdp.horizon) :
    successorLocalCharge mdp defaultState episodes delta trajectory n
        (mdp.horizon - (stage.val + 1)) (by omega)
        (trajectory (n + 1) 0 stage).state =
      generatedPairLocalCharge mdp episodes delta trajectory
        (trajectory (n + 1) 0 stage).state
        (trajectory (n + 1) 0 stage).action (n + 1) := by
  have hstep := successorBatchAligned_step haligned stage
  have hstage : mdp.decisionStageRemaining
      (mdp.horizon - (stage.val + 1)) (by omega) = stage := by
    apply Fin.ext
    simp [MDP.decisionStageRemaining]
    omega
  have haction : (trajectory (n + 1) 0 stage).action =
      successorPolicyTable mdp defaultState episodes delta trajectory n stage
        (trajectory (n + 1) 0 stage).state := by
    rw [hstep.1]
    exact hstep.2
  have hcount := batchedPrefixCount_generatedBatchAggregateVisitIncrement
    trajectory (trajectory (n + 1) 0 stage).state
      (trajectory (n + 1) 0 stage).action n
  have hcount' : batchedPrefixCount
      (generatedBatchAggregateVisitIncrement trajectory
        (trajectory (n + 1) 0 stage).state
        (trajectory (n + 1) 0 stage).action) (n + 1) =
      (adaptiveCumulativeEmpiricalModelStateAt trajectory n).1.aggregateVisitCount
        (trajectory (n + 1) 0 stage).state
        (trajectory (n + 1) 0 stage).action := by
    simpa [adaptiveCumulativeAggregateVisitCountAt] using hcount
  unfold successorLocalCharge generatedPairLocalCharge
  simp only [successorSummary]
  rw [hstage, ← haction, ← hcount']

/-- One generated episode's unweighted local charge is exactly the sum of
pair charges repeated by the actual state-action visit multiplicities. -/
theorem sum_successorLocalCharge_eq_sum_pairIncrement_mul_charge_of_aligned
    {mdp : MDP State Action} {defaultState : State}
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1} {n : Nat}
    (haligned : SuccessorBatchAligned mdp defaultState episodes delta trajectory n) :
    (∑ stage : Fin mdp.horizon,
      successorLocalCharge mdp defaultState episodes delta trajectory n
        (mdp.horizon - (stage.val + 1)) (by omega)
        (trajectory (n + 1) 0 stage).state) =
      ∑ state : State, ∑ action : Action,
        (generatedBatchAggregateVisitIncrement trajectory state action (n + 1) : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action (n + 1) := by
  simp_rw [successorLocalCharge_eq_generatedPairLocalCharge_of_aligned haligned]
  simp_rw [generatedBatchAggregateVisitIncrement_eq_indicatorSum]
  calc
    (∑ stage : Fin mdp.horizon,
        generatedPairLocalCharge mdp episodes delta trajectory
          (trajectory (n + 1) 0 stage).state
          (trajectory (n + 1) 0 stage).action (n + 1)) =
      ∑ stage : Fin mdp.horizon, ∑ state : State, ∑ action : Action,
        (if (trajectory (n + 1) 0 stage).state = state ∧
          (trajectory (n + 1) 0 stage).action = action then 1 else 0 : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action (n + 1) := by
        apply Finset.sum_congr rfl
        intro stage _
        symm
        rw [Finset.sum_eq_single (trajectory (n + 1) 0 stage).state]
        · rw [Finset.sum_eq_single (trajectory (n + 1) 0 stage).action]
          · simp
          · intro action _ hne
            simp [hne, Ne.symm hne]
          · simp
        · intro state _ hne
          simp [hne, Ne.symm hne]
        · simp
    _ = ∑ state : State, ∑ action : Action, ∑ stage : Fin mdp.horizon,
        (if (trajectory (n + 1) 0 stage).state = state ∧
          (trajectory (n + 1) 0 stage).action = action then 1 else 0 : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action (n + 1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro state _
      apply Finset.sum_congr rfl
      intro action _
      rw [← Finset.sum_mul]
      norm_num

/-- Chronological global stage corresponding to a coordinate of a remaining
suffix. -/
def remainingGlobalStage (mdp : MDP State Action) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon) (stage : Fin remaining) :
    Fin mdp.horizon :=
  ⟨mdp.horizon - remaining + stage.val, by omega⟩

theorem successorLocalCharge_eq_of_remaining_eq
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat)
    {left right : Nat} (hleft : left + 1 <= mdp.horizon)
    (hright : right + 1 <= mdp.horizon) (h : left = right) (state : State) :
    successorLocalCharge mdp defaultState episodes delta trajectory n
        left hleft state =
      successorLocalCharge mdp defaultState episodes delta trajectory n
        right hright state := by
  subst right
  rfl

/-- Proof-irrelevant chronological wrapper around the remaining-indexed local
charge.  Keeping the proof argument out of finite sums avoids dependent
rewrites in the charge telescope. -/
noncomputable def successorStageLocalCharge
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat)
    (stage : Fin mdp.horizon) (state : State) : Real :=
  successorLocalCharge mdp defaultState episodes delta trajectory n
    (mdp.horizon - (stage.val + 1)) (by omega) state

/-- The recursive charge is exactly its chronological finite sum. -/
theorem successorWeightedChargeFrom_eq_sum
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (n : Nat) :
    forall (remaining : Nat) (hremaining : remaining <= mdp.horizon)
      (state : State) (trace : StepTrace Action State remaining),
      successorWeightedChargeFrom mdp defaultState episodes delta trajectory n
          remaining hremaining state trace =
        ∑ stage : Fin remaining,
          normalizedBellmanChargeWeight mdp
              (remainingGlobalStage mdp remaining hremaining stage) *
            successorStageLocalCharge mdp defaultState episodes delta trajectory n
              (remainingGlobalStage mdp remaining hremaining stage)
              (StepTrace.stateAt state trace stage) := by
  intro remaining
  induction remaining with
  | zero =>
      intro hremaining state trace
      simp [successorWeightedChargeFrom]
  | succ remaining ih =>
      intro hremaining state trace
      rw [successorWeightedChargeFrom, Fin.sum_univ_succ]
      have hheadStage : remainingGlobalStage mdp (remaining + 1) hremaining 0 =
          mdp.decisionStageRemaining remaining hremaining := by
        apply Fin.ext
        change mdp.horizon - (remaining + 1) + 0 =
          mdp.horizon - (remaining + 1)
        omega
      have hheadLocal : successorLocalCharge mdp defaultState episodes delta
            trajectory n remaining hremaining state =
          successorStageLocalCharge mdp defaultState episodes delta trajectory n
            (mdp.decisionStageRemaining remaining hremaining) state := by
        unfold successorStageLocalCharge
        apply successorLocalCharge_eq_of_remaining_eq
        change remaining = mdp.horizon -
          (mdp.horizon - (remaining + 1) + 1)
        omega
      have hhead : normalizedBellmanChargeWeight mdp
              (mdp.decisionStageRemaining remaining hremaining) *
            successorLocalCharge mdp defaultState episodes delta trajectory n
              remaining hremaining state =
          normalizedBellmanChargeWeight mdp
              (remainingGlobalStage mdp (remaining + 1) hremaining 0) *
            successorStageLocalCharge mdp defaultState episodes delta trajectory n
              (remainingGlobalStage mdp (remaining + 1) hremaining 0)
              (StepTrace.stateAt state trace 0) := by
        rw [hheadStage, hheadLocal]
        rw [StepTrace.stateAt_zero_apply]
      rw [hhead]
      congr 1
      have htail : remaining <= mdp.horizon := by omega
      rw [ih htail (trace 0).2 (Fin.tail trace)]
      apply Finset.sum_congr rfl
      intro stage _
      have hglobal : remainingGlobalStage mdp remaining htail stage =
          remainingGlobalStage mdp (remaining + 1) hremaining stage.succ := by
        exact Fin.ext (by
          change mdp.horizon - remaining + stage.val =
            mdp.horizon - (remaining + 1) + (stage.val + 1)
          omega)
      have hstate := StepTrace.stateAt_succ state (trace 0) (Fin.tail trace) stage
      rw [hglobal]
      exact congrArg
        (fun currentState =>
          normalizedBellmanChargeWeight mdp
              (remainingGlobalStage mdp (remaining + 1) hremaining stage.succ) *
            successorStageLocalCharge mdp defaultState episodes delta trajectory n
              (remainingGlobalStage mdp (remaining + 1) hremaining stage.succ)
              currentState)
        (by simpa using hstate.symm)

/-- On an aligned generated successor batch, the recursively reconstructed
canonical charge is the chronological recorded charge sum. -/
theorem successorCanonicalWeightedCharge_eq_successorWeightedChargeSum_of_aligned
    {mdp : MDP State Action} {defaultState : State}
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1} {n : Nat}
    (haligned : SuccessorBatchAligned mdp defaultState episodes delta trajectory n) :
    successorCanonicalWeightedCharge mdp defaultState episodes delta trajectory n =
      successorWeightedChargeSum mdp defaultState episodes delta trajectory n := by
  rw [successorCanonicalWeightedCharge,
    successorWeightedChargeFrom_eq_sum]
  unfold successorWeightedChargeSum
  apply Finset.sum_congr rfl
  intro stage _
  simp only [remainingGlobalStage, Nat.sub_self, zero_add]
  unfold successorStageLocalCharge
  have hstate := (successorBatchAligned_step haligned stage).1
  have htraceState : StepTrace.stateAt
      ((trajectory (n + 1)).reconstructedInitialState defaultState)
      ((trajectory (n + 1)).reconstructedStepTrace) stage =
        mdp.trajectoryStateAt
          ((trajectory (n + 1)).reconstructedInitialState defaultState,
            (trajectory (n + 1)).reconstructedStepTrace) stage := by
    exact mdp.stepTrace_stateAt_eq_trajectoryStateAt
      (trajectory :=
        ((trajectory (n + 1)).reconstructedInitialState defaultState,
          (trajectory (n + 1)).reconstructedStepTrace)) stage
  rw [htraceState, ← hstate]

/-- One aligned canonical successor charge is dominated by its unweighted
state-action multiplicity sum. -/
theorem successorCanonicalWeightedCharge_le_sum_pairIncrement_mul_charge_of_aligned
    {mdp : MDP State Action} {defaultState : State}
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1} {n : Nat}
    (hhorizon : 0 < mdp.horizon)
    (haligned : SuccessorBatchAligned mdp defaultState episodes delta trajectory n) :
    successorCanonicalWeightedCharge mdp defaultState episodes delta trajectory n <=
      ∑ state : State, ∑ action : Action,
        (generatedBatchAggregateVisitIncrement trajectory state action (n + 1) : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action (n + 1) := by
  rw [successorCanonicalWeightedCharge_eq_successorWeightedChargeSum_of_aligned
    haligned]
  calc
    successorWeightedChargeSum mdp defaultState episodes delta trajectory n <=
        ∑ stage : Fin mdp.horizon,
          successorLocalCharge mdp defaultState episodes delta trajectory n
            (mdp.horizon - (stage.val + 1)) (by omega)
            (trajectory (n + 1) 0 stage).state := by
      unfold successorWeightedChargeSum
      apply Finset.sum_le_sum
      intro stage _
      exact mul_le_of_le_one_left
        (successorLocalCharge_nonneg mdp defaultState episodes delta trajectory n
          (mdp.horizon - (stage.val + 1)) (by omega)
          (trajectory (n + 1) 0 stage).state)
        (normalizedBellmanChargeWeight_mem_Icc mdp hhorizon stage).2
    _ = _ :=
      sum_successorLocalCharge_eq_sum_pairIncrement_mul_charge_of_aligned haligned

/-- Total pair charge over the first `episodes` generated batches. -/
noncomputable def totalGeneratedPairCharge
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) : Real :=
  ∑ state : State, ∑ action : Action,
    (Finset.range episodes).sum fun episode =>
      (generatedBatchAggregateVisitIncrement trajectory state action episode : Real) *
        generatedPairLocalCharge mdp episodes delta trajectory state action episode

theorem generatedPairChargeTerm_nonneg
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) (episode : Nat) :
    0 <= (generatedBatchAggregateVisitIncrement trajectory state action episode : Real) *
      generatedPairLocalCharge mdp episodes delta trajectory state action episode :=
  mul_nonneg (Nat.cast_nonneg _)
    (generatedPairLocalCharge_nonneg mdp episodes delta trajectory state action episode)

private theorem sum_range_succ_shift_le_sum_range
    (f : Nat -> Real) (rounds : Nat) (hf : forall n, 0 <= f n) :
    (Finset.range (rounds - 1)).sum (fun n => f (n + 1)) <=
      (Finset.range rounds).sum f := by
  cases rounds with
  | zero => simp
  | succ rounds =>
      rw [Nat.add_sub_cancel]
      induction rounds with
      | zero => simp [hf]
      | succ rounds ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          have hzero : 0 <= f 0 := hf 0
          simpa [add_comm] using add_le_add_right ih (f (rounds + 1))

/-- Summing all aligned successor episodes is dominated by the all-batch pair
charge ledger; coordinate zero appears only on the right and is nonnegative. -/
theorem sum_successorCanonicalWeightedCharge_le_totalGeneratedPairCharge
    {mdp : MDP State Action} {defaultState : State}
    {episodes : Nat} {delta : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (hhorizon : 0 < mdp.horizon)
    (haligned : forall n, n + 1 < episodes ->
      SuccessorBatchAligned mdp defaultState episodes delta trajectory n) :
    (Finset.range (episodes - 1)).sum (fun n =>
      successorCanonicalWeightedCharge mdp defaultState episodes delta trajectory n) <=
      totalGeneratedPairCharge mdp episodes delta trajectory := by
  calc
    _ <= (Finset.range (episodes - 1)).sum (fun n =>
        ∑ state : State, ∑ action : Action,
          (generatedBatchAggregateVisitIncrement trajectory state action (n + 1) : Real) *
            generatedPairLocalCharge mdp episodes delta trajectory state action
              (n + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact successorCanonicalWeightedCharge_le_sum_pairIncrement_mul_charge_of_aligned
        hhorizon (haligned n (by have := Finset.mem_range.mp hn; omega))
    _ = ∑ state : State, ∑ action : Action,
        (Finset.range (episodes - 1)).sum (fun n =>
          (generatedBatchAggregateVisitIncrement trajectory state action (n + 1) : Real) *
            generatedPairLocalCharge mdp episodes delta trajectory state action
              (n + 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.sum_comm]
    _ <= totalGeneratedPairCharge mdp episodes delta trajectory := by
      unfold totalGeneratedPairCharge
      apply Finset.sum_le_sum
      intro state _
      apply Finset.sum_le_sum
      intro action _
      exact sum_range_succ_shift_le_sum_range
        (fun episode =>
          (generatedBatchAggregateVisitIncrement trajectory state action episode : Real) *
            generatedPairLocalCharge mdp episodes delta trajectory state action episode)
        episodes (generatedPairChargeTerm_nonneg mdp episodes delta trajectory state action)

private theorem min_add_le_add_min {cap x y : Real}
    (hx : 0 <= x) : min cap (x + y) <= x + min cap y := by
  by_cases hy : cap <= y
  · exact (min_le_left _ _).trans (by linarith [min_eq_left hy])
  · rw [min_eq_right (le_of_not_ge hy)]
    exact min_le_right _ _

/-- Natural threshold at which the clipped reciprocal correction starts its
logarithmic telescope. -/
noncomputable def reciprocalChargeThreshold
    (mdp : MDP State Action) (episodes : Nat) (delta : Real) : Nat :=
  Nat.ceil (66 * Fintype.card State * (mdp.horizon : Real) *
    logFactor (State := State) (Action := Action) mdp episodes delta)

/-- Exact one-pair accounting before the final paper-constant simplification. -/
theorem sum_generatedPairCharge_le_accounting
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action)
    (hhorizon : 0 < mdp.horizon)
    (hlog : 1 <= logFactor (State := State) (Action := Action)
      mdp episodes delta) :
    (Finset.range episodes).sum (fun episode =>
        (generatedBatchAggregateVisitIncrement trajectory state action episode : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action episode) <=
      (mdp.horizon : Real) * (1 + mdp.horizon) +
      (9 * (mdp.horizon : Real) *
        logFactor (State := State) (Action := Action) mdp episodes delta) *
        (2 * Real.sqrt (batchedPrefixCount
            (generatedBatchAggregateVisitIncrement trajectory state action) episodes) +
          2 * mdp.horizon + 2 * mdp.horizon *
            Real.log ((max 1 (batchedPrefixCount
              (generatedBatchAggregateVisitIncrement trajectory state action)
              episodes) : Nat) : Real)) +
      (mdp.horizon : Real) *
        (reciprocalChargeThreshold (State := State) (Action := Action)
          mdp episodes delta + mdp.horizon) +
      2 * (66 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
        logFactor (State := State) (Action := Action) mdp episodes delta) *
        Real.log ((max 1 (batchedPrefixCount
          (generatedBatchAggregateVisitIncrement trajectory state action)
          episodes) : Nat) : Real) := by
  let increment := generatedBatchAggregateVisitIncrement trajectory state action
  let count := batchedPrefixCount increment
  let L := logFactor (State := State) (Action := Action) mdp episodes delta
  let a : Real := 9 * (mdp.horizon : Real) * L
  let b : Real := 66 * Fintype.card State * (mdp.horizon : Real) ^ 2 * L
  let threshold := reciprocalChargeThreshold (State := State) (Action := Action)
    mdp episodes delta
  have hinc : forall episode, increment episode <= mdp.horizon :=
    generatedBatchAggregateVisitIncrement_le_horizon trajectory state action
  have hH : (0 : Real) <= mdp.horizon := by positivity
  have ha : 0 <= a := by
    dsimp [a, L]
    positivity
  have hb : 0 <= b := by
    dsimp [b, L]
    positivity
  have hpoint (episode : Nat) :
      (increment episode : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action episode <=
        if count episode = 0 then
          (increment episode : Real) * mdp.horizon
        else
          a * ((increment episode : Real) / Real.sqrt (count episode)) +
            (increment episode : Real) * min (mdp.horizon : Real)
              (b / count episode) := by
    unfold generatedPairLocalCharge
    change (increment episode : Real) *
        (if count episode = 0 then _ else _) <= _
    by_cases hz : count episode = 0
    · simp [hz]
    · rw [if_neg hz, if_neg hz]
      have hsplit := min_add_le_add_min (cap := (mdp.horizon : Real))
        (x := a / Real.sqrt (count episode))
        (y := b / count episode) (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hsplit
        (Nat.cast_nonneg (increment episode))
      dsimp [a, b, L, count, increment] at hmul ⊢
      convert hmul using 1 <;> ring
  have hsumPoint : (Finset.range episodes).sum (fun episode =>
        (increment episode : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action episode) <=
      (Finset.range episodes).sum (fun episode =>
        if count episode = 0 then
          (increment episode : Real) * mdp.horizon
        else
          a * ((increment episode : Real) / Real.sqrt (count episode)) +
            (increment episode : Real) * min (mdp.horizon : Real)
              (b / count episode)) :=
    Finset.sum_le_sum fun episode _ => hpoint episode
  have hsplit : (Finset.range episodes).sum (fun episode =>
        if count episode = 0 then
          (increment episode : Real) * mdp.horizon
        else
          a * ((increment episode : Real) / Real.sqrt (count episode)) +
            (increment episode : Real) * min (mdp.horizon : Real)
              (b / count episode)) =
      (mdp.horizon : Real) * (Finset.range episodes).sum (fun episode =>
        if count episode = 0 then (increment episode : Real) else 0) +
      a * (Finset.range episodes).sum (fun episode =>
        if count episode = 0 then 0 else
          (increment episode : Real) / Real.sqrt (count episode)) +
      (Finset.range episodes).sum (fun episode =>
        if count episode = 0 then 0 else
          (increment episode : Real) * min (mdp.horizon : Real)
            (b / count episode)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro episode _
    by_cases hz : count episode = 0 <;> simp [hz] <;> ring
  rw [hsplit] at hsumPoint
  have hzeroNat := sum_low_batchedIncrement_le increment mdp.horizon 1 episodes
    hinc
  have hzero : (Finset.range episodes).sum (fun episode =>
      if count episode = 0 then (increment episode : Real) else 0) <=
      (1 + mdp.horizon : Nat) := by
    exact_mod_cast (by simpa [count] using hzeroNat)
  have hsqrt := sum_positive_batchedInvSqrt_le increment mdp.horizon episodes
    hhorizon hinc
  have hthreshold : mdp.horizon <= threshold := by
    have hreal : (mdp.horizon : Real) <=
        66 * Fintype.card State * (mdp.horizon : Real) * L := by
      have hcard : (1 : Real) <= Fintype.card State := by
        exact_mod_cast Fintype.card_pos
      dsimp [L]
      nlinarith
    have hcast : (mdp.horizon : Real) <= (threshold : Real) := by
      dsimp [threshold, reciprocalChargeThreshold]
      exact hreal.trans (Nat.le_ceil _)
    exact_mod_cast hcast
  have hrecip := sum_positive_batchedMinReciprocal_le increment mdp.horizon
    threshold episodes (mdp.horizon : Real) b hhorizon hthreshold hinc hH hb
  have hzeroMul := mul_le_mul_of_nonneg_left hzero hH
  have hsqrtMul := mul_le_mul_of_nonneg_left hsqrt ha
  have htotal := add_le_add (add_le_add hzeroMul hsqrtMul) hrecip
  norm_num only [Nat.cast_add, Nat.cast_one] at htotal
  dsimp [count, increment, a, b, L, threshold] at hsumPoint htotal ⊢
  exact hsumPoint.trans (by simpa [add_assoc] using htotal)

/-- The accounting ledger fits the explicit per-pair `18/238` budget. -/
theorem sum_generatedPairCharge_le_explicit
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action)
    (hhorizon : 0 < mdp.horizon)
    (hlog : 1 <= logFactor (State := State) (Action := Action)
      mdp episodes delta)
    (hlogCount : Real.log ((max 1 (batchedPrefixCount
        (generatedBatchAggregateVisitIncrement trajectory state action)
        episodes) : Nat) : Real) <=
      logFactor (State := State) (Action := Action) mdp episodes delta) :
    (Finset.range episodes).sum (fun episode =>
        (generatedBatchAggregateVisitIncrement trajectory state action episode : Real) *
          generatedPairLocalCharge mdp episodes delta trajectory state action episode) <=
      18 * (mdp.horizon : Real) *
          logFactor (State := State) (Action := Action) mdp episodes delta *
          Real.sqrt (batchedPrefixCount
            (generatedBatchAggregateVisitIncrement trajectory state action) episodes) +
        238 * Fintype.card State * (mdp.horizon : Real) ^ 2 *
          logFactor (State := State) (Action := Action) mdp episodes delta ^ 2 := by
  let H : Real := mdp.horizon
  let S : Real := Fintype.card State
  let L := logFactor (State := State) (Action := Action) mdp episodes delta
  let N := batchedPrefixCount
    (generatedBatchAggregateVisitIncrement trajectory state action) episodes
  let logN := Real.log ((max 1 N : Nat) : Real)
  let threshold := reciprocalChargeThreshold (State := State) (Action := Action)
    mdp episodes delta
  have haccount := sum_generatedPairCharge_le_accounting mdp episodes delta
    trajectory state action hhorizon hlog
  have hH : 1 <= H := by
    dsimp [H]
    exact_mod_cast hhorizon
  have hS : 1 <= S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos
  have hL : 1 <= L := hlog
  have hlogN0 : 0 <= logN := by
    dsimp [logN]
    exact Real.log_nonneg (by exact_mod_cast le_max_left 1 N)
  have hlogN : logN <= L := hlogCount
  have hx : 0 <= 66 * S * H * L := by positivity
  have hceil := Nat.ceil_lt_add_one hx
  have hthreshold : (threshold : Real) <= 67 * S * H * L := by
    dsimp [threshold, reciprocalChargeThreshold, S, H, L]
    have hunit : (1 : Real) <=
        (Fintype.card State : Real) * mdp.horizon *
          logFactor (State := State) (Action := Action) mdp episodes delta := by
      have hSH : (1 : Real) * 1 <= S * H :=
        mul_le_mul hS hH (by norm_num) (le_trans zero_le_one hS)
      have hSH' : (1 : Real) <= S * H := by simpa using hSH
      have hSHL : (1 : Real) * 1 <= (S * H) * L :=
        mul_le_mul hSH' hL (by norm_num)
          (mul_nonneg (le_trans zero_le_one hS) (le_trans zero_le_one hH))
      simpa [S, H, L] using hSHL
    nlinarith
  have hbase : H * (1 + H) <= 2 * S * H ^ 2 * L ^ 2 := by
    have hsmall : H * (1 + H) <= 2 * H ^ 2 := by nlinarith
    have hLsq : 1 <= L ^ 2 := by nlinarith
    have hscaleS : H ^ 2 <= S * H ^ 2 := by
      have := mul_le_mul_of_nonneg_right hS (sq_nonneg H)
      nlinarith
    have hscaleL : S * H ^ 2 <= S * H ^ 2 * L ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hLsq
        (mul_nonneg (le_trans zero_le_one hS) (sq_nonneg H))
    linarith
  have hsqrtCorrection :
      (9 * H * L) * (2 * H + 2 * H * logN) <=
        36 * S * H ^ 2 * L ^ 2 := by
    have honeLog : 1 + logN <= 2 * L := by linarith
    have hfactor : 0 <= 18 * H ^ 2 * L := by positivity
    have hraw := mul_le_mul_of_nonneg_left honeLog hfactor
    have hscale : 36 * H ^ 2 * L ^ 2 <= 36 * S * H ^ 2 * L ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hS
        (mul_nonneg (sq_nonneg H) (sq_nonneg L))]
    nlinarith
  have hreciprocal :
      H * ((threshold : Real) + H) +
          2 * (66 * S * H ^ 2 * L) * logN <=
        200 * S * H ^ 2 * L ^ 2 := by
    have hHscale : H <= S * H * L := by
      have hSL : (1 : Real) * 1 <= S * L :=
        mul_le_mul hS hL (by norm_num) (le_trans zero_le_one hS)
      have hmul := mul_le_mul_of_nonneg_left hSL (le_trans zero_le_one hH)
      nlinarith
    have hthresholdSum : (threshold : Real) + H <= 68 * S * H * L := by
      linarith
    have hfirst := mul_le_mul_of_nonneg_left hthresholdSum
      (le_trans zero_le_one hH)
    have hsecond : 2 * (66 * S * H ^ 2 * L) * logN <=
        132 * S * H ^ 2 * L ^ 2 := by
      have hfactor : 0 <= 132 * S * H ^ 2 * L := by positivity
      have := mul_le_mul_of_nonneg_left hlogN hfactor
      nlinarith
    nlinarith
  calc
    _ <= _ := haccount
    _ <= _ := by
      have hcorr := add_le_add (add_le_add hbase hsqrtCorrection) hreciprocal
      have hlead := add_le_add_left hcorr (18 * H * L * Real.sqrt N)
      dsimp [H, S, L, N, logN, threshold] at hlead ⊢
      nlinarith

/-- On the positive task domain the paper logarithmic factor is at least one.
The factor `5` in the confidence numerator is deliberately retained here: it
is what makes the statement true uniformly for every `delta <= 1`. -/
theorem one_le_logFactor
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    1 <= logFactor (State := State) (Action := Action)
      mdp episodes delta := by
  have hproduct :
      1 <= mdp.horizon * Fintype.card State * Fintype.card Action *
        (episodes * mdp.horizon) := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [ne_eq, mul_eq_zero]
      exact not_or_intro (not_or_intro (not_or_intro hhorizon.ne'
        Fintype.card_ne_zero) Fintype.card_ne_zero)
        (not_or_intro hepisodes.ne' hhorizon.ne'))
  have hnumerator :
      5 <= confidenceNumerator (State := State) (Action := Action)
        mdp episodes := by
    unfold confidenceNumerator totalSteps
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 5 hproduct
  have hnumeratorReal :
      (5 : Real) <=
        (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat) := by
    exact_mod_cast hnumerator
  have hnumeratorNonneg :
      0 <= (confidenceNumerator (State := State) (Action := Action)
        mdp episodes : Nat) := by positivity
  have hdivide :
      (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat) <=
        (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat) / delta := by
    apply (le_div_iff₀ hdelta).2
    nlinarith
  rw [logFactor_eq_paper mdp episodes delta hhorizon hepisodes
    hdelta hdelta_le_one]
  rw [Real.le_log_iff_exp_le (div_pos (by positivity) hdelta)]
  exact (le_of_lt Real.exp_one_lt_three).trans
    ((show (3 : Real) <= 5 by norm_num).trans
      (hnumeratorReal.trans hdivide))

/-- A single state-action pair is visited at most once per stage, hence at
most `episodes * H` times in the complete generated ledger. -/
theorem batchedPrefixCount_generatedBatchAggregateVisitIncrement_le_totalSteps
    (mdp : MDP State Action) (episodes : Nat)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action) :
    batchedPrefixCount
        (generatedBatchAggregateVisitIncrement trajectory state action)
        episodes <= totalSteps mdp episodes := by
  unfold batchedPrefixCount totalSteps
  calc
    (Finset.range episodes).sum (fun episode =>
        generatedBatchAggregateVisitIncrement trajectory state action episode) <=
      (Finset.range episodes).sum (fun _ => mdp.horizon) :=
        Finset.sum_le_sum fun episode _ =>
          generatedBatchAggregateVisitIncrement_le_horizon
            trajectory state action episode
    _ = episodes * mdp.horizon := by simp

/-- The logarithm of every final pair count is controlled by the single paper
logarithmic factor used by the generated policy. -/
theorem log_max_batchedPrefixCount_le_logFactor
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (state : State) (action : Action)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    Real.log ((max 1 (batchedPrefixCount
        (generatedBatchAggregateVisitIncrement trajectory state action)
        episodes) : Nat) : Real) <=
      logFactor (State := State) (Action := Action) mdp episodes delta := by
  let N := batchedPrefixCount
    (generatedBatchAggregateVisitIncrement trajectory state action) episodes
  let T := totalSteps mdp episodes
  have hTpos : 0 < T := by
    dsimp [T, totalSteps]
    positivity
  have hN : N <= T := by
    dsimp [N, T]
    exact batchedPrefixCount_generatedBatchAggregateVisitIncrement_le_totalSteps
      mdp episodes trajectory state action
  have hmax : max 1 N <= T := max_le (Nat.one_le_iff_ne_zero.mpr hTpos.ne') hN
  have hTleNumerator :
      T <= confidenceNumerator (State := State) (Action := Action)
        mdp episodes := by
    have hfactor : 1 <=
        5 * mdp.horizon * Fintype.card State * Fintype.card Action := by
      have hfactorPos : 0 <
          5 * mdp.horizon * Fintype.card State * Fintype.card Action := by
        positivity
      omega
    calc
      T = 1 * T := by simp
      _ <= (5 * mdp.horizon * Fintype.card State * Fintype.card Action) * T :=
        Nat.mul_le_mul_right T hfactor
      _ = confidenceNumerator (State := State) (Action := Action)
          mdp episodes := by
        simp [T, confidenceNumerator, totalSteps, Nat.mul_assoc]
  have hNumeratorDiv :
      (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat) <=
        (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat) / delta := by
    apply (le_div_iff₀ hdelta).2
    have hnonneg :
        0 <= (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat) := Nat.zero_le _
    nlinarith
  have hpositive : (0 : Real) < (max 1 N : Nat) := by positivity
  have hargument :
      ((max 1 N : Nat) : Real) <=
        (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat) / delta := by
    have hcast :
        ((max 1 N : Nat) : Real) <=
          (confidenceNumerator (State := State) (Action := Action)
            mdp episodes : Nat) := by
      exact_mod_cast hmax.trans hTleNumerator
    exact hcast.trans hNumeratorDiv
  rw [logFactor_eq_paper mdp episodes delta hhorizon hepisodes
    hdelta hdelta_le_one]
  exact Real.strictMonoOn_log.monotoneOn hpositive
    (div_pos (by
      exact_mod_cast hTpos.trans_le hTleNumerator) hdelta) hargument

/-- The aggregate count ledger is exact: summing final counts over every
state-action pair gives the number `episodes * H` of generated transitions. -/
theorem sum_batchedPrefixCount_generatedBatchAggregateVisitIncrement_eq_totalSteps
    (mdp : MDP State Action) (episodes : Nat)
    (trajectory : EpisodeBatchTrajectory mdp 1) :
    (∑ state : State, ∑ action : Action,
        batchedPrefixCount
          (generatedBatchAggregateVisitIncrement trajectory state action)
          episodes) = totalSteps mdp episodes := by
  unfold batchedPrefixCount totalSteps
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [sum_generatedBatchAggregateVisitIncrement_eq_horizon trajectory]
  simp

/-- Cauchy--Schwarz converts the exact visit ledger into the canonical
`sqrt(S A K H)` exploration scale. -/
theorem sum_sqrt_batchedPrefixCount_le
    (mdp : MDP State Action) (episodes : Nat)
    (trajectory : EpisodeBatchTrajectory mdp 1) :
    (∑ state : State, ∑ action : Action,
        Real.sqrt (batchedPrefixCount
          (generatedBatchAggregateVisitIncrement trajectory state action)
          episodes)) <=
      Real.sqrt (totalSteps mdp episodes : Nat) *
        Real.sqrt ((Fintype.card State * Fintype.card Action : Nat) : Real) := by
  have hcs := Real.sum_sqrt_mul_sqrt_le
    (Finset.univ : Finset (State × Action))
    (f := fun pair =>
      (batchedPrefixCount
        (generatedBatchAggregateVisitIncrement trajectory pair.1 pair.2)
        episodes : Real))
    (g := fun _ => (1 : Real))
    (fun _ => Nat.cast_nonneg _)
    (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_ofNat, one_mul] at hcs
  have hcountProd :
      (∑ pair : State × Action,
          (batchedPrefixCount
            (generatedBatchAggregateVisitIncrement trajectory pair.1 pair.2)
            episodes : Real)) = (totalSteps mdp episodes : Nat) := by
    rw [Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd]
    exact_mod_cast
      sum_batchedPrefixCount_generatedBatchAggregateVisitIncrement_eq_totalSteps
        mdp episodes trajectory
  rw [hcountProd] at hcs
  rw [Fintype.sum_prod_type] at hcs
  simp only [Prod.fst, Prod.snd] at hcs
  simpa [Fintype.card_prod] using hcs

/-- Global deterministic charge budget for every generated batch in the
canonical recurrent UCBVI-CH ledger.  The two square-root factors are kept
separate here so the exact total-count identity remains visible. -/
theorem totalGeneratedPairCharge_le_explicit
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    totalGeneratedPairCharge mdp episodes delta trajectory <=
      18 * (mdp.horizon : Real) *
          logFactor (State := State) (Action := Action) mdp episodes delta *
          (Real.sqrt (totalSteps mdp episodes : Nat) *
            Real.sqrt ((Fintype.card State * Fintype.card Action : Nat) : Real)) +
        238 * (Fintype.card State : Real) ^ 2 *
          Fintype.card Action * (mdp.horizon : Real) ^ 2 *
          logFactor (State := State) (Action := Action)
            mdp episodes delta ^ 2 := by
  let H : Real := mdp.horizon
  let S : Real := Fintype.card State
  let A : Real := Fintype.card Action
  let L := logFactor (State := State) (Action := Action) mdp episodes delta
  let N := fun state action => batchedPrefixCount
    (generatedBatchAggregateVisitIncrement trajectory state action) episodes
  have hlog : 1 <= L := one_le_logFactor mdp episodes delta
    hhorizon hepisodes hdelta hdelta_le_one
  have hpair (state : State) (action : Action) :
      (Finset.range episodes).sum (fun episode =>
          (generatedBatchAggregateVisitIncrement trajectory state action episode : Real) *
            generatedPairLocalCharge mdp episodes delta trajectory
              state action episode) <=
        18 * H * L * Real.sqrt (N state action) +
          238 * S * H ^ 2 * L ^ 2 := by
    dsimp [H, S, L, N]
    exact sum_generatedPairCharge_le_explicit mdp episodes delta trajectory
      state action hhorizon hlog
      (log_max_batchedPrefixCount_le_logFactor mdp episodes delta trajectory
        state action hhorizon hepisodes hdelta hdelta_le_one)
  have hsum := Finset.sum_le_sum fun state (_ : state ∈ (Finset.univ : Finset State)) =>
    Finset.sum_le_sum fun action (_ : action ∈ (Finset.univ : Finset Action)) =>
      hpair state action
  have hsqrt := sum_sqrt_batchedPrefixCount_le mdp episodes trajectory
  have hleadNonneg : 0 <= 18 * H * L := by
    dsimp [H, L]
    positivity
  have hlead := mul_le_mul_of_nonneg_left hsqrt hleadNonneg
  have hleadEq :
      (∑ state : State, ∑ action : Action,
          18 * H * L * Real.sqrt (N state action)) =
        (18 * H * L) *
          (∑ state : State, ∑ action : Action,
            Real.sqrt (N state action)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _
    rw [Finset.mul_sum]
  have haddEq :
      (∑ _state : State, ∑ _action : Action,
          238 * S * H ^ 2 * L ^ 2) =
        238 * S ^ 2 * A * H ^ 2 * L ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [S, A]
    norm_num only [Nat.cast_mul]
    ring
  unfold totalGeneratedPairCharge
  calc
    _ <= ∑ state : State, ∑ action : Action,
        (18 * H * L * Real.sqrt (N state action) +
          238 * S * H ^ 2 * L ^ 2) := hsum
    _ = (18 * H * L) *
          (∑ state : State, ∑ action : Action,
            Real.sqrt (N state action)) +
        238 * S ^ 2 * A * H ^ 2 * L ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      rw [hleadEq, haddEq]
    _ <= (18 * H * L) *
          (Real.sqrt (totalSteps mdp episodes : Nat) *
            Real.sqrt ((Fintype.card State * Fintype.card Action : Nat) : Real)) +
        238 * S ^ 2 * A * H ^ 2 * L ^ 2 :=
      add_le_add hlead (le_refl _)
    _ = _ := by
      dsimp [H, S, A, L]

end AdaptiveCumulativeHoeffdingUCBVI
end BanditRLProof.FiniteHorizonRL
