import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeInverseSqrtHighProbabilityAverageConsistency
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Exploratory behavior regret transport

This module transports cumulative expected-regret certificates from deterministic
recommended policies to the exploratory behavior policies actually used by the
adaptive source.  The explicit charge is linear in the exploration rate and
quadratic in the horizon.  For a fixed exploration rate, the vanishing statistical
certificate therefore converges to that charge, not to zero.
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

namespace DeterministicMarkovPolicyTable

theorem exploratoryActionPMF_apply
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    table.exploratoryActionPMF explorationRate hexplorationRate
        stage state action =
      (explorationRate : ENNReal) * (Fintype.card Action : ENNReal)⁻¹ +
        ((1 - explorationRate : NNReal) : ENNReal) *
          if action = table stage state then 1 else 0 := by
  rw [exploratoryActionPMF, PMF.bind_apply]
  rw [tsum_fintype, Fintype.sum_bool]
  simp [PMF.bernoulli_apply, PMF.uniformOfFintype_apply, PMF.pure_apply]

theorem integral_exploratoryActionPMF
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) (f : Action -> Real) :
    (∫ action, f action ∂
        (table.exploratoryActionPMF explorationRate hexplorationRate
          stage state).toMeasure) =
      (explorationRate : Real) *
          (∑ action, f action) / (Fintype.card Action : Real) +
        (1 - (explorationRate : Real)) * f (table stage state) := by
  rw [PMF.integral_eq_sum]
  calc
    (∑ x,
        (table.exploratoryActionPMF explorationRate hexplorationRate
          stage state x).toReal • f x) =
        ∑ x,
          (((explorationRate : ENNReal) *
                (Fintype.card Action : ENNReal)⁻¹).toReal +
            (((1 - explorationRate : NNReal) : ENNReal) *
                if x = table stage state then 1 else 0).toReal) * f x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [show table.exploratoryActionPMF explorationRate hexplorationRate
          stage state x =
          (explorationRate : ENNReal) *
              (Fintype.card Action : ENNReal)⁻¹ +
            (((1 - explorationRate : NNReal) : ENNReal) *
              if x = table stage state then 1 else 0) by
        rw [exploratoryActionPMF, PMF.bind_apply]
        rw [tsum_fintype, Fintype.sum_bool]
        simp [PMF.bernoulli_apply, PMF.uniformOfFintype_apply, PMF.pure_apply]]
      rw [ENNReal.toReal_add] <;> try finiteness
      rfl
    _ = (explorationRate : Real) *
          (∑ action, f action) / (Fintype.card Action : Real) +
        (1 - (explorationRate : Real)) * f (table stage state) := by
      simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, add_mul]
      rw [Finset.sum_add_distrib]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      norm_cast
      simp only [apply_ite, Nat.cast_one, Nat.cast_zero, ite_mul,
        mul_zero, one_mul, zero_mul]
      rw [show (∑ x : Action,
            if x = table stage state then
              ((1 - explorationRate : NNReal) : Real) * f x else 0) =
          ((1 - explorationRate : NNReal) : Real) * f (table stage state) by
        simpa using
          (Finset.sum_ite_eq' (Finset.univ : Finset Action)
            (table stage state)
            (fun x => ((1 - explorationRate : NNReal) : Real) * f x))]
      rw [NNReal.coe_sub hexplorationRate]
      norm_num
      ring

theorem selected_sub_integral_exploratoryActionPMF_le
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) (f : Action -> Real)
    (bound : Real) (hbound : forall action, |f action| <= bound) :
    f (table stage state) -
        (∫ action, f action ∂
          (table.exploratoryActionPMF explorationRate hexplorationRate
            stage state).toMeasure) <=
      2 * (explorationRate : Real) * bound := by
  rw [table.integral_exploratoryActionPMF explorationRate hexplorationRate
    stage state f]
  have hcardPos : (0 : Real) < Fintype.card Action := by
    exact_mod_cast Fintype.card_pos
  have hsumLower :
      (Fintype.card Action : Real) * (-bound) <= ∑ action, f action := by
    calc
      (Fintype.card Action : Real) * (-bound) = ∑ _action : Action, -bound := by
        simp
      _ <= ∑ action, f action := by
        apply Finset.sum_le_sum
        intro action _haction
        exact (abs_le.mp (hbound action)).1
  have haverageLower :
      -bound <= (∑ action, f action) / (Fintype.card Action : Real) := by
    rw [le_div_iff₀ hcardPos]
    nlinarith
  have hselectedUpper : f (table stage state) <= bound :=
    (abs_le.mp (hbound (table stage state))).2
  have hgap :
      f (table stage state) -
          (∑ action, f action) / (Fintype.card Action : Real) <=
        2 * bound := by
    linarith
  have hp : 0 <= (explorationRate : Real) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hgap hp
  calc
    f (table stage state) -
          ((explorationRate : Real) *
              (∑ action, f action) / (Fintype.card Action : Real) +
            (1 - (explorationRate : Real)) * f (table stage state)) =
        (explorationRate : Real) *
          (f (table stage state) -
            (∑ action, f action) / (Fintype.card Action : Real)) := by ring
    _ <= (explorationRate : Real) * (2 * bound) := hscaled
    _ = 2 * (explorationRate : Real) * bound := by ring

end DeterministicMarkovPolicyTable

namespace MDP

/-- A bounded continuation gives a bounded one-step action value. -/
theorem bellmanQ_abs_le
    (mdp : MDP State Action) (rewardBound continuationBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    {value : State -> Real}
    (hvalue : forall state, |value state| <= continuationBound)
    (state : State) (action : Action) :
    |mdp.bellmanQ value state action| <= rewardBound + continuationBound := by
  have htransition :
      |mdp.transitionValue value state action| <= continuationBound := by
    rw [← Real.norm_eq_abs]
    have hnorm := norm_integral_le_of_norm_le_const
      (μ := mdp.transition (state, action)) (C := continuationBound)
      (Filter.Eventually.of_forall fun nextState => by
        rw [Real.norm_eq_abs]
        exact hvalue nextState)
    simpa [MDP.transitionValue] using hnorm
  unfold bellmanQ
  exact (abs_add_le _ _).trans
    (add_le_add (hrewardBound state action) htransition)

/-- A pointwise continuation difference bound transports through one transition kernel. -/
theorem transitionValue_sub_le_const
    (mdp : MDP State Action) {left right : State -> Real} {bound : Real}
    (hbound : forall state, left state - right state <= bound)
    (state : State) (action : Action) :
    mdp.transitionValue left state action -
        mdp.transitionValue right state action <= bound := by
  have hleft : Integrable left (mdp.transition (state, action)) :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  have hright : Integrable right (mdp.transition (state, action)) :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  unfold transitionValue
  rw [← integral_sub hleft hright]
  calc
    (∫ nextState, left nextState - right nextState ∂
        mdp.transition (state, action)) <=
        ∫ _nextState, bound ∂mdp.transition (state, action) := by
      apply integral_mono
      · exact hleft.sub hright
      · exact integrable_const bound
      · exact hbound
    _ = bound := by simp

end MDP

namespace MarkovPolicy

/-- Every bounded-reward policy value is bounded by remaining horizon times the reward bound. -/
theorem valueRemaining_abs_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) (state : State) :
    |policy.valueRemaining remaining hremaining state| <=
      (remaining : Real) * rewardBound := by
  induction remaining generalizing state with
  | zero =>
      simp [valueRemaining]
  | succ remaining ih =>
      rw [valueRemaining]
      rw [← Real.norm_eq_abs]
      have hnorm := norm_integral_le_of_norm_le_const
        (μ := policy.actionKernel
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state)
        (C := ((remaining + 1 : Nat) : Real) * rewardBound)
        (Filter.Eventually.of_forall fun action => by
          rw [Real.norm_eq_abs]
          calc
            |mdp.bellmanQ
                (policy.valueRemaining remaining (by omega)) state action| <=
                rewardBound + (remaining : Real) * rewardBound :=
              mdp.bellmanQ_abs_le rewardBound ((remaining : Real) * rewardBound)
                hrewardBound (fun nextState => ih (by omega) nextState) state action
            _ = ((remaining + 1 : Nat) : Real) * rewardBound := by
              push_cast
              ring)
      simpa [MarkovPolicy.bellman] using hnorm

end MarkovPolicy

namespace DeterministicMarkovPolicyTable

/-- Bellman evaluation of a deterministic table selects exactly its table action. -/
theorem toMarkovPolicy_bellman
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (stage : Fin mdp.horizon) (value : State -> Real) (state : State) :
    table.toMarkovPolicy.bellman stage value state =
      mdp.bellmanQ value state (table stage state) := by
  unfold MarkovPolicy.bellman toMarkovPolicy
  rw [ProbabilityTheory.Kernel.deterministic_apply]
  rw [integral_dirac']
  exact
    ((mdp.measurable_bellmanQ (measurable_of_finite value)).comp
      (measurable_const.prodMk measurable_id)).stronglyMeasurable

/-- Bellman evaluation of the exploratory table is its explicit PMF mixture. -/
theorem exploratoryPolicy_bellman
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (value : State -> Real) (state : State) :
    (table.exploratoryPolicy explorationRate hexplorationRate).bellman
        stage value state =
      (explorationRate : Real) *
          (∑ action, mdp.bellmanQ value state action) /
            (Fintype.card Action : Real) +
        (1 - (explorationRate : Real)) *
          mdp.bellmanQ value state (table stage state) := by
  unfold MarkovPolicy.bellman exploratoryPolicy
  change (∫ action, mdp.bellmanQ value state action ∂
      (table.exploratoryActionPMF explorationRate hexplorationRate
        stage state).toMeasure) = _
  exact table.integral_exploratoryActionPMF explorationRate hexplorationRate
    stage state (fun action => mdp.bellmanQ value state action)

/--
Exploration around a deterministic table loses at most the explicit quadratic-horizon charge.
The charge is linear in the exploration rate and reward bound.
-/
theorem toMarkovPolicy_valueRemaining_sub_exploratoryPolicy_valueRemaining_le
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) (state : State) :
    table.toMarkovPolicy.valueRemaining remaining hremaining state -
        (table.exploratoryPolicy explorationRate hexplorationRate).valueRemaining
          remaining hremaining state <=
      (explorationRate : Real) * rewardBound * (remaining : Real) *
        ((remaining + 1 : Nat) : Real) := by
  induction remaining generalizing state with
  | zero =>
      simp [MarkovPolicy.valueRemaining]
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let deterministicTail :=
        table.toMarkovPolicy.valueRemaining remaining (by omega)
      let exploratoryTail :=
        (table.exploratoryPolicy explorationRate hexplorationRate).valueRemaining
          remaining (by omega)
      have hpropagation :
          table.toMarkovPolicy.bellman stage deterministicTail state -
              table.toMarkovPolicy.bellman stage exploratoryTail state <=
            (explorationRate : Real) * rewardBound * (remaining : Real) *
              ((remaining + 1 : Nat) : Real) := by
        rw [table.toMarkovPolicy_bellman, table.toMarkovPolicy_bellman]
        unfold MDP.bellmanQ
        have htransition := mdp.transitionValue_sub_le_const
          (left := deterministicTail) (right := exploratoryTail)
          (bound := (explorationRate : Real) * rewardBound * (remaining : Real) *
            ((remaining + 1 : Nat) : Real))
          (fun nextState => ih (by omega) nextState) state (table stage state)
        linarith
      have hactionValue (action : Action) :
          |mdp.bellmanQ exploratoryTail state action| <=
            ((remaining + 1 : Nat) : Real) * rewardBound := by
        exact (mdp.bellmanQ_abs_le rewardBound
          ((remaining : Real) * rewardBound) hrewardBound
          (fun nextState =>
            (table.exploratoryPolicy explorationRate hexplorationRate).valueRemaining_abs_le
              rewardBound hrewardBound remaining (by omega) nextState)
          state action).trans_eq (by
            push_cast
            ring)
      have hexplorationStep :
          table.toMarkovPolicy.bellman stage exploratoryTail state -
              (table.exploratoryPolicy explorationRate hexplorationRate).bellman
                stage exploratoryTail state <=
            2 * (explorationRate : Real) *
              (((remaining + 1 : Nat) : Real) * rewardBound) := by
        rw [table.toMarkovPolicy_bellman]
        unfold MarkovPolicy.bellman exploratoryPolicy
        change mdp.bellmanQ exploratoryTail state (table stage state) -
            (∫ action, mdp.bellmanQ exploratoryTail state action ∂
              (table.exploratoryActionPMF explorationRate hexplorationRate
                stage state).toMeasure) <= _
        exact table.selected_sub_integral_exploratoryActionPMF_le
          explorationRate hexplorationRate stage state
          (fun action => mdp.bellmanQ exploratoryTail state action)
          (((remaining + 1 : Nat) : Real) * rewardBound) hactionValue
      rw [MarkovPolicy.valueRemaining, MarkovPolicy.valueRemaining]
      change table.toMarkovPolicy.bellman stage deterministicTail state -
          (table.exploratoryPolicy explorationRate hexplorationRate).bellman
            stage exploratoryTail state <= _
      calc
        table.toMarkovPolicy.bellman stage deterministicTail state -
              (table.exploratoryPolicy explorationRate hexplorationRate).bellman
                stage exploratoryTail state =
            (table.toMarkovPolicy.bellman stage deterministicTail state -
              table.toMarkovPolicy.bellman stage exploratoryTail state) +
            (table.toMarkovPolicy.bellman stage exploratoryTail state -
              (table.exploratoryPolicy explorationRate hexplorationRate).bellman
                stage exploratoryTail state) := by ring
        _ <= (explorationRate : Real) * rewardBound * (remaining : Real) *
              ((remaining + 1 : Nat) : Real) +
            2 * (explorationRate : Real) *
              (((remaining + 1 : Nat) : Real) * rewardBound) :=
          add_le_add hpropagation hexplorationStep
        _ = (explorationRate : Real) * rewardBound *
              ((remaining + 1 : Nat) : Real) *
              ((remaining + 2 : Nat) : Real) := by
          push_cast
          ring

/-- Exploratory-behavior expected regret is bounded by table regret plus its exploration charge. -/
theorem exploratoryPolicy_expectedRegret_le_toMarkovPolicy_expectedRegret_add_charge
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound) :
    (table.exploratoryPolicy explorationRate hexplorationRate).expectedRegret
        initialState <=
      table.toMarkovPolicy.expectedRegret initialState +
        (explorationRate : Real) * rewardBound * (mdp.horizon : Real) *
          ((mdp.horizon + 1 : Nat) : Real) := by
  let charge := (explorationRate : Real) * rewardBound *
    (mdp.horizon : Real) * ((mdp.horizon + 1 : Nat) : Real)
  have hvalueGap (state : State) :
      table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state -
          (table.exploratoryPolicy explorationRate hexplorationRate).valueAt
            0 (Nat.zero_le mdp.horizon) state <= charge := by
    simpa [MarkovPolicy.valueAt, charge] using
      table.toMarkovPolicy_valueRemaining_sub_exploratoryPolicy_valueRemaining_le
        explorationRate hexplorationRate rewardBound hrewardBound
        mdp.horizon le_rfl state
  rw [MarkovPolicy.expectedRegret_eq_integral_optimalValueAt_sub_valueAt
    (table.exploratoryPolicy explorationRate hexplorationRate) initialState]
  rw [MarkovPolicy.expectedRegret_eq_integral_optimalValueAt_sub_valueAt
    table.toMarkovPolicy initialState]
  have hoptimalSubTable : Integrable
      (fun state =>
        mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
          table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state)
      initialState :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  have htableSubExploratory : Integrable
      (fun state =>
        table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state -
          (table.exploratoryPolicy explorationRate hexplorationRate).valueAt
            0 (Nat.zero_le mdp.horizon) state)
      initialState :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  calc
    (∫ state,
        mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
          (table.exploratoryPolicy explorationRate hexplorationRate).valueAt
            0 (Nat.zero_le mdp.horizon) state ∂initialState) =
        (∫ state,
          (mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
            table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state) +
          (table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state -
            (table.exploratoryPolicy explorationRate hexplorationRate).valueAt
              0 (Nat.zero_le mdp.horizon) state) ∂initialState) := by
      apply integral_congr_ae
      filter_upwards [] with state
      ring
    _ = (∫ state,
          mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
            table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state
            ∂initialState) +
        ∫ state,
          table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state -
            (table.exploratoryPolicy explorationRate hexplorationRate).valueAt
              0 (Nat.zero_le mdp.horizon) state ∂initialState := by
      rw [integral_add hoptimalSubTable htableSubExploratory]
    _ <= (∫ state,
          mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
            table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state
            ∂initialState) +
        ∫ _state, charge ∂initialState := by
      apply add_le_add (le_refl _)
      apply integral_mono
      · exact htableSubExploratory
      · exact integrable_const charge
      · exact hvalueGap
    _ = (∫ state,
          mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
            table.toMarkovPolicy.valueAt 0 (Nat.zero_le mdp.horizon) state
            ∂initialState) +
        (explorationRate : Real) * rewardBound * (mdp.horizon : Real) *
          ((mdp.horizon + 1 : Nat) : Real) := by
      simp [charge]

end DeterministicMarkovPolicyTable

/-- The per-policy price of uniform exploration over a bounded-reward horizon. -/
noncomputable def exploratoryBehaviorRegretCharge
    (mdp : MDP State Action) (explorationRate : NNReal)
    (rewardBound : Real) : Real :=
  (explorationRate : Real) * rewardBound * (mdp.horizon : Real) *
    ((mdp.horizon + 1 : Nat) : Real)

/-- Sum of expected regrets of exploratory behaviors centered on cumulative recommendations. -/
noncomputable def adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (((cumulativeTransitionCountSummaryAt trajectory round)
        |>.countRadiusOptimisticPolicyTable mdp defaultState countRadius)
      |>.exploratoryPolicy explorationRate hexplorationRate).expectedRegret initialState

/-- Average expected regret of those exploratory behaviors. -/
noncomputable def adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) : Real :=
  adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
      (initialState := initialState) trajectory defaultState countRadius
      explorationRate hexplorationRate rounds /
    (rounds : Real)

/-- Cumulative exploratory behavior regret is bounded by recommendation regret plus one charge per round. -/
theorem adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (rounds : Nat) :
    adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState countRadius
        explorationRate hexplorationRate rounds <=
      adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState countRadius rounds +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
  unfold adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
    adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
  calc
    (∑ round : Fin rounds,
        (((cumulativeTransitionCountSummaryAt trajectory round)
            |>.countRadiusOptimisticPolicyTable mdp defaultState countRadius)
          |>.exploratoryPolicy explorationRate hexplorationRate).expectedRegret
            initialState) <=
        ∑ round : Fin rounds,
          ((adaptiveCumulativeEmpiricalOptimisticPlanAt trajectory defaultState
              countRadius round).optimisticPolicy.expectedRegret initialState +
            exploratoryBehaviorRegretCharge mdp explorationRate rewardBound) := by
      apply Finset.sum_le_sum
      intro round _hround
      let summary := cumulativeTransitionCountSummaryAt trajectory round
      let table := summary.countRadiusOptimisticPolicyTable
        mdp defaultState countRadius
      have htransport :=
        table.exploratoryPolicy_expectedRegret_le_toMarkovPolicy_expectedRegret_add_charge
          initialState explorationRate hexplorationRate rewardBound hrewardBound
      simpa [summary, table, exploratoryBehaviorRegretCharge,
        adaptiveCumulativeEmpiricalOptimisticPlanAt,
        TransitionCountSummary.countRadiusOptimisticPolicyTable_toMarkovPolicy]
        using htransport
    _ = (∑ round : Fin rounds,
          (adaptiveCumulativeEmpiricalOptimisticPlanAt trajectory defaultState
            countRadius round).optimisticPolicy.expectedRegret initialState) +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
      rw [Finset.sum_add_distrib]
      simp

/-- For a nonempty window, averaging removes the repeated-round factor from the charge. -/
theorem adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (rounds : Nat) (hrounds : 0 < rounds) :
    adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState countRadius
        explorationRate hexplorationRate rounds <=
      adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState countRadius rounds +
        exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
  unfold adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
    adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
  have hroundsReal : (0 : Real) < rounds := by exact_mod_cast hrounds
  have hsum :=
    adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret_le
      (initialState := initialState) trajectory defaultState countRadius
      explorationRate hexplorationRate
      rewardBound hrewardBound rounds
  calc
    adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
          (initialState := initialState) trajectory defaultState countRadius
          explorationRate hexplorationRate rounds /
        (rounds : Real) <=
      (adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState countRadius rounds +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound) /
        (rounds : Real) :=
      (div_le_div_iff_of_pos_right hroundsReal).2 hsum
    _ = adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState countRadius rounds /
          (rounds : Real) +
        exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
      field_simp

namespace AdaptiveEpisodeBatchSource

/-- The finite-window behavior-regret certificate adds the explicit exploration charge. -/
noncomputable def vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegretBound
    (mdp : MDP State Action) (n : Nat) (visitFloor : Real)
    (explorationRate : NNReal) : Real :=
  vanishingDeltaScheduledAverageRecommendedExpectedRegretBound mdp n visitFloor +
    exploratoryBehaviorRegretCharge mdp explorationRate 1

/-- With a fixed exploration rate, the deterministic certificate tends to its exploration charge. -/
theorem vanishingDeltaScheduledAverageExploratoryBehaviorBound_tendsto_charge
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (visitFloor : Real) (hvisitFloor : 0 < visitFloor)
    (explorationRate : NNReal) :
    Filter.Tendsto
      (fun n =>
        vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegretBound
          mdp n visitFloor explorationRate)
      Filter.atTop
      (nhds (exploratoryBehaviorRegretCharge mdp explorationRate 1)) := by
  unfold vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegretBound
  simpa using
    (vanishingDeltaScheduledAverageBound_tendsto_zero
      mdp hhorizon visitFloor hvisitFloor).add tendsto_const_nhds

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

omit [Nonempty State] in
/--
The regret term indexed by `round` is the source's successor behavior at coordinate
`round + 1`; the initial behavior at coordinate zero is intentionally excluded.
-/
theorem exploratorySource_policyAt_succ_eq_cumulativeOptimisticExploratoryPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat) :
    (exploratorySource mdp initialState episodes initialTable defaultState
      countRadius explorationRate hexplorationRate).policyAt trajectory (round + 1) =
      ((cumulativeTransitionCountSummaryAt trajectory round)
        |>.countRadiusOptimisticPolicyTable mdp defaultState countRadius
        |>.exploratoryPolicy explorationRate hexplorationRate) := by
  rfl

/-- Trajectories whose average exploratory-behavior regret exceeds its charged certificate. -/
noncomputable def vanishingDeltaScheduledAverageExploratoryBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (n : Nat) (visitFloor : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    Set
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor)) :=
  {trajectory |
    AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegretBound
          mdp n visitFloor explorationRate <
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
          mdp (n + 1)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
            visitFloor)
        explorationRate hexplorationRate (n + 1)}

/--
Finite-window high-probability endpoint for successor exploratory behaviors at source coordinates
`1` through `n + 1`; the initial-table behavior at coordinate zero is not charged here.
The violation set is contained in the measurable count bad event; outside that event, optimism and
the charged average behavior-regret certificate hold simultaneously.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (n : Nat) (visitFloor : Real)
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor))]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hvisitFloor : 0 < visitFloor) :
    let episodes :=
      AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
        mdp n visitFloor
    let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp (n + 1) delta visitFloor
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate hexplorationRate
    let violationSet :=
      vanishingDeltaScheduledAverageExploratoryBehaviorRegretViolationSet
        mdp initialState defaultState n visitFloor explorationRate hexplorationRate
    MeasurableSet (source.adaptiveCumulativeCountBadEvent (n + 1) delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent (n + 1) delta) <=
        ENNReal.ofReal delta /\
      violationSet ⊆ source.adaptiveCumulativeCountBadEvent (n + 1) delta /\
      source.trajectoryMeasure violationSet <= ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent (n + 1) delta ->
        (forall round : Fin (n + 1), forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius
            explorationRate hexplorationRate (n + 1) <=
          AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegretBound
              mdp n visitFloor explorationRate := by
  let episodes :=
    AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes mdp n visitFloor
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let countRadius :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
      mdp (n + 1) delta visitFloor
  let source := exploratorySource mdp initialState episodes initialTable
    defaultState countRadius explorationRate hexplorationRate
  let violationSet :=
    vanishingDeltaScheduledAverageExploratoryBehaviorRegretViolationSet
      mdp initialState defaultState n visitFloor explorationRate hexplorationRate
  have hparent :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_vanishingDeltaScheduledAverageRecommendedExpectedRegret
      mdp initialState n visitFloor initialTable defaultState explorationRate
      hexplorationRate support hfloor hrewardBound hhorizon hvisitFloor
  dsimp only at hparent
  rcases hparent with ⟨hmeasurable, hbadTail, _hrecommendedSubset,
    _hrecommendedTail, houtside⟩
  have hbehaviorOutside : forall trajectory,
      trajectory ∉ source.adaptiveCumulativeCountBadEvent (n + 1) delta ->
      (forall round : Fin (n + 1), forall state,
        mdp.optimalValueRemaining mdp.horizon le_rfl state <=
          (adaptiveCumulativeEmpiricalOptimisticPlanAt
            trajectory defaultState countRadius round).upperValueRemaining
              mdp.horizon le_rfl state) /\
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
          (initialState := initialState) trajectory defaultState countRadius
          explorationRate hexplorationRate (n + 1) <=
        AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegretBound
            mdp n visitFloor explorationRate := by
    intro trajectory htrajectory
    have hrecommendation := houtside trajectory htrajectory
    refine ⟨hrecommendation.1, ?_⟩
    have htransport :=
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret_le
        (initialState := initialState) trajectory defaultState countRadius
        explorationRate hexplorationRate 1 hrewardBound (n + 1) (by omega)
    apply htransport.trans
    unfold AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageExploratoryBehaviorExpectedRegretBound
    exact add_le_add hrecommendation.2 (le_refl _)
  have hsubset :
      violationSet ⊆ source.adaptiveCumulativeCountBadEvent (n + 1) delta := by
    intro trajectory hviolation
    by_contra houtsideBad
    have hbound := (hbehaviorOutside trajectory houtsideBad).2
    exact (not_lt_of_ge hbound) hviolation
  have hviolationTail :
      source.trajectoryMeasure violationSet <= ENNReal.ofReal delta :=
    (measure_mono hsubset).trans hbadTail
  exact ⟨hmeasurable, hbadTail, hsubset, hviolationTail, hbehaviorOutside⟩

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
