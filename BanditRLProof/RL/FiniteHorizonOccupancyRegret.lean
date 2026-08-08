import BanditRLProof.RL.FiniteHorizonOptimality
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Finite-horizon occupancy regret identity

This module connects finite-horizon Bellman optimality to expected trajectory
regret.  It constructs chronological state occupancies, records the expected
one-step Bellman optimality gap under a policy, and recursively sums those gaps
along the policy-induced state laws.  The resulting occupancy functional is
exactly the difference between optimal and policy value, hence exactly the
expected trajectory regret.  The measurable greedy policy has zero regret.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [MeasurableSingletonClass State] [Nonempty Action]

namespace MarkovPolicy

/-- State law at a chronological stage under a Markov policy. -/
noncomputable def stateOccupancy
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) :
    (stage : Nat) -> stage <= mdp.horizon -> Measure State
  | 0, _ => initialState
  | stage + 1, hstage =>
      policy.inducedStateKernel ⟨stage, by omega⟩ ∘ₘ
        policy.stateOccupancy initialState stage (by omega)

/-- Every chronological state occupancy is a probability measure. -/
instance instStateOccupancyIsProbabilityMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Nat) (hstage : stage <= mdp.horizon) :
    IsProbabilityMeasure (policy.stateOccupancy initialState stage hstage) := by
  induction stage with
  | zero =>
      rw [stateOccupancy]
      infer_instance
  | succ stage ih =>
      rw [stateOccupancy]
      letI : IsProbabilityMeasure
          (policy.stateOccupancy initialState stage (by omega)) :=
        ih (by omega)
      infer_instance

/--
Expected one-step optimality gap after averaging the optimal action-value gap
over the policy action kernel at a chronological stage.
-/
noncomputable def policyBellmanGap
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (state : State) : Real :=
  mdp.optimalValueAt stage (Nat.le_of_lt stage.isLt) state -
    policy.bellman stage
      (mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt)) state

/-- The policy-averaged one-step Bellman optimality gap is measurable. -/
theorem measurable_policyBellmanGap
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) :
    Measurable (policy.policyBellmanGap stage) := by
  exact (mdp.measurable_optimalValueAt stage (Nat.le_of_lt stage.isLt)).sub
    (policy.measurable_bellman stage
      (mdp.measurable_optimalValueAt (stage + 1)
        (Nat.succ_le_of_lt stage.isLt)))

/-- Every policy-averaged one-step Bellman optimality gap is nonnegative. -/
theorem policyBellmanGap_nonneg
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (state : State) :
    0 <= policy.policyBellmanGap stage state := by
  unfold policyBellmanGap
  rw [mdp.optimalValueAt_bellman stage stage.isLt]
  exact sub_nonneg.mpr
    (policy.bellman_le_optimalBellman stage
      (mdp.optimalValueAt (stage + 1)
        (Nat.succ_le_of_lt stage.isLt)) state)

omit [MeasurableSingletonClass State] in
/-- Reindex a chronological policy Bellman gap by the number of decisions remaining. -/
theorem policyBellmanGap_stageOfRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    policy.policyBellmanGap
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state =
      mdp.optimalValueRemaining (remaining + 1) hremaining state -
        policy.bellman ⟨mdp.horizon - (remaining + 1), by omega⟩
          (mdp.optimalValueRemaining remaining (by omega)) state := by
  unfold policyBellmanGap MDP.optimalValueAt
  have hcurrent := mdp.optimalValueRemaining_eq_of_eq
    (Nat.sub_le mdp.horizon (mdp.horizon - (remaining + 1))) hremaining
    (by omega : mdp.horizon - (mdp.horizon - (remaining + 1)) = remaining + 1)
  have htail := mdp.optimalValueRemaining_eq_of_eq
    (Nat.sub_le mdp.horizon (mdp.horizon - (remaining + 1) + 1)) (by omega)
    (by omega : mdp.horizon - (mdp.horizon - (remaining + 1) + 1) = remaining)
  rw [hcurrent, htail]

omit [Nonempty Action] in
/-- Integrating a continuation value against the induced state kernel averages its transition
expectation over the policy action kernel. -/
theorem integral_inducedStateKernel_eq_integral_transitionValue
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (value : State -> Real)
    (state : State) :
    (∫ nextState, value nextState ∂policy.inducedStateKernel stage state) =
      ∫ action, mdp.transitionValue value state action
        ∂policy.actionKernel stage state := by
  have hvalue : Measurable value := measurable_of_finite _
  have hpair : Integrable (fun pair : Action × State => value pair.2)
      ((policy.actionKernel stage).compProd mdp.transition state) := by
    apply integrable_of_fintype
    exact hvalue.comp measurable_snd
  unfold inducedStateKernel
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_snd]
  rw [integral_map measurable_snd.aemeasurable hvalue.aestronglyMeasurable]
  rw [ProbabilityTheory.integral_compProd hpair]
  rfl

omit [Nonempty Action] in
/-- Changing only the continuation value in a policy Bellman step is integration against the
induced next-state kernel. -/
theorem bellman_sub_bellman_eq_integral_inducedStateKernel_sub
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (left right : State -> Real)
    (state : State) :
    policy.bellman stage left state - policy.bellman stage right state =
      ∫ nextState, left nextState - right nextState
        ∂policy.inducedStateKernel stage state := by
  have hleftState : Integrable left (policy.inducedStateKernel stage state) :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  have hrightState : Integrable right (policy.inducedStateKernel stage state) :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  rw [integral_sub hleftState hrightState]
  rw [policy.integral_inducedStateKernel_eq_integral_transitionValue stage left state]
  rw [policy.integral_inducedStateKernel_eq_integral_transitionValue stage right state]
  unfold bellman
  have hleftBellmanQ : Measurable
      (fun action => mdp.bellmanQ left state action) :=
    (mdp.measurable_bellmanQ (measurable_of_finite left)).comp
      (measurable_const.prodMk measurable_id)
  have hrightBellmanQ : Measurable
      (fun action => mdp.bellmanQ right state action) :=
    (mdp.measurable_bellmanQ (measurable_of_finite right)).comp
      (measurable_const.prodMk measurable_id)
  have hleftAction : Integrable
      (fun action => mdp.bellmanQ left state action)
      (policy.actionKernel stage state) :=
    integrable_of_fintype _ _ hleftBellmanQ
  have hrightAction : Integrable
      (fun action => mdp.bellmanQ right state action)
      (policy.actionKernel stage state) :=
    integrable_of_fintype _ _ hrightBellmanQ
  have hleftTransition : Integrable
      (fun action => mdp.transitionValue left state action)
      (policy.actionKernel stage state) :=
    integrable_of_fintype _ _
      ((mdp.measurable_transitionValue (measurable_of_finite left)).comp
        (measurable_const.prodMk measurable_id))
  have hrightTransition : Integrable
      (fun action => mdp.transitionValue right state action)
      (policy.actionKernel stage state) :=
    integrable_of_fintype _ _
      ((mdp.measurable_transitionValue (measurable_of_finite right)).comp
        (measurable_const.prodMk measurable_id))
  rw [← integral_sub hleftAction hrightAction]
  rw [← integral_sub hleftTransition hrightTransition]
  apply integral_congr_ae
  filter_upwards [] with action
  simp only [MDP.bellmanQ]
  ring

omit [Nonempty Action] in
/-- Push an integrated continuation-value difference through one policy-induced state step. -/
theorem integral_sub_comp_inducedStateKernel_eq_integral_bellman_sub
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (left right : State -> Real)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    (∫ nextState, left nextState - right nextState
        ∂policy.inducedStateKernel stage ∘ₘ mu) =
      ∫ state, policy.bellman stage left state -
        policy.bellman stage right state ∂mu := by
  have hsub : Measurable (fun state => left state - right state) :=
    (measurable_of_finite left).sub (measurable_of_finite right)
  rw [← Measure.snd_compProd mu (policy.inducedStateKernel stage)]
  rw [Measure.snd]
  rw [integral_map measurable_snd.aemeasurable hsub.aestronglyMeasurable]
  have hpair : Integrable
      (fun pair : State × State => left pair.2 - right pair.2)
      (mu.compProd (policy.inducedStateKernel stage)) := by
    apply integrable_of_fintype
    exact hsub.comp measurable_snd
  rw [Measure.integral_compProd hpair]
  apply integral_congr_ae
  filter_upwards [] with state
  exact (policy.bellman_sub_bellman_eq_integral_inducedStateKernel_sub
    stage left right state).symm

/--
Finite occupancy sum of policy Bellman gaps, indexed by decisions remaining.
Each recursive call advances the state law by the policy-induced kernel.
-/
noncomputable def occupancyGapRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp) :
    (remaining : Nat) -> remaining <= mdp.horizon -> Measure State -> Real
  | 0, _, _ => 0
  | remaining + 1, hremaining, mu =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      (∫ state,
          mdp.optimalValueRemaining (remaining + 1) hremaining state -
            policy.bellman stage
              (mdp.optimalValueRemaining remaining (by omega)) state ∂mu) +
        policy.occupancyGapRemaining remaining (by omega)
          (policy.inducedStateKernel stage ∘ₘ mu)

omit [MeasurableSingletonClass State] in
/-- The successor recursion is an integral of the chronological policy Bellman gap plus the
remaining occupancy gaps under the next-state law. -/
theorem occupancyGapRemaining_succ
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (mu : Measure State) :
    policy.occupancyGapRemaining (remaining + 1) hremaining mu =
      (∫ state, policy.policyBellmanGap
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state ∂mu) +
        policy.occupancyGapRemaining remaining (by omega)
          (policy.inducedStateKernel
            ⟨mdp.horizon - (remaining + 1), by omega⟩ ∘ₘ mu) := by
  rw [occupancyGapRemaining]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with state
  exact (policy.policyBellmanGap_stageOfRemaining remaining hremaining state).symm

/-- The recursive occupancy-gap sum is exactly the integrated optimal-policy value gap. -/
theorem occupancyGapRemaining_eq_integral_optimalValueRemaining_sub_valueRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    policy.occupancyGapRemaining remaining hremaining mu =
      ∫ state, mdp.optimalValueRemaining remaining hremaining state -
        policy.valueRemaining remaining hremaining state ∂mu := by
  induction remaining generalizing mu with
  | zero =>
      simp [occupancyGapRemaining, MDP.optimalValueRemaining, valueRemaining]
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let nextMu : Measure State := policy.inducedStateKernel stage ∘ₘ mu
      letI : IsProbabilityMeasure nextMu := by
        dsimp [nextMu]
        infer_instance
      rw [occupancyGapRemaining]
      rw [ih (by omega) nextMu]
      rw [policy.integral_sub_comp_inducedStateKernel_eq_integral_bellman_sub
        stage
        (mdp.optimalValueRemaining remaining (by omega))
        (policy.valueRemaining remaining (by omega)) mu]
      rw [valueRemaining]
      have hfirst : Integrable
          (fun state =>
            mdp.optimalValueRemaining (remaining + 1) hremaining state -
              policy.bellman stage
                (mdp.optimalValueRemaining remaining (by omega)) state) mu :=
        integrable_of_fintype _ _ (measurable_of_finite _)
      have hsecond : Integrable
          (fun state =>
            policy.bellman stage
                (mdp.optimalValueRemaining remaining (by omega)) state -
              policy.bellman stage
                (policy.valueRemaining remaining (by omega)) state) mu :=
        integrable_of_fintype _ _ (measurable_of_finite _)
      rw [← integral_add hfirst hsecond]
      apply integral_congr_ae
      filter_upwards [] with state
      ring

/-- Backward policy value is bounded by backward optimal value. -/
theorem valueRemaining_le_optimalValueRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) :
    policy.valueRemaining remaining hremaining state <=
      mdp.optimalValueRemaining remaining hremaining state := by
  induction remaining generalizing state with
  | zero =>
      rfl
  | succ remaining ih =>
      rw [valueRemaining, MDP.optimalValueRemaining]
      exact
        (policy.bellman_mono
          (stage := ⟨mdp.horizon - (remaining + 1), by omega⟩)
          (fun nextState => ih (by omega) nextState) state).trans
        (policy.bellman_le_optimalBellman
          ⟨mdp.horizon - (remaining + 1), by omega⟩
          (mdp.optimalValueRemaining remaining (by omega)) state)

/-- The finite occupancy Bellman-gap sum is nonnegative. -/
theorem occupancyGapRemaining_nonneg
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    0 <= policy.occupancyGapRemaining remaining hremaining mu := by
  rw [policy.occupancyGapRemaining_eq_integral_optimalValueRemaining_sub_valueRemaining]
  apply integral_nonneg
  intro state
  exact sub_nonneg.mpr
    (policy.valueRemaining_le_optimalValueRemaining remaining hremaining state)

/-- Expected finite-horizon regret: optimal initial value minus generated trajectory reward. -/
noncomputable def expectedRegret
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) : Real :=
  (∫ state, mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state ∂initialState) -
    ∫ trajectory, mdp.cumulativeReward trajectory
      ∂policy.trajectoryMeasure initialState

/-- Expected trajectory regret is the initial-law integral of the optimal-policy value gap. -/
theorem expectedRegret_eq_integral_optimalValueAt_sub_valueAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState] :
    policy.expectedRegret initialState =
      ∫ state,
        mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
          policy.valueAt 0 (Nat.zero_le mdp.horizon) state ∂initialState := by
  unfold expectedRegret
  rw [policy.integral_cumulativeReward_trajectoryMeasure_eq_integral_valueAt_zero]
  have hoptimal : Integrable
      (mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon)) initialState :=
    integrable_of_fintype _ _
      (mdp.measurable_optimalValueAt 0 (Nat.zero_le mdp.horizon))
  have hpolicy : Integrable
      (policy.valueAt 0 (Nat.zero_le mdp.horizon)) initialState :=
    integrable_of_fintype _ _
      (policy.measurable_valueAt 0 (Nat.zero_le mdp.horizon))
  exact (integral_sub hoptimal hpolicy).symm

/-- Expected trajectory regret equals the full recursively accumulated occupancy Bellman gap. -/
theorem expectedRegret_eq_occupancyGapRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState] :
    policy.expectedRegret initialState =
      policy.occupancyGapRemaining mdp.horizon le_rfl initialState := by
  rw [policy.expectedRegret_eq_integral_optimalValueAt_sub_valueAt]
  rw [policy.occupancyGapRemaining_eq_integral_optimalValueRemaining_sub_valueRemaining]
  rfl

/-- Expected finite-horizon regret is nonnegative. -/
theorem expectedRegret_nonneg
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState] :
    0 <= policy.expectedRegret initialState := by
  rw [policy.expectedRegret_eq_occupancyGapRemaining]
  exact policy.occupancyGapRemaining_nonneg mdp.horizon le_rfl initialState

end MarkovPolicy

namespace MDP

/-- The measurable greedy policy has zero expected finite-horizon regret. -/
theorem optimalPolicy_expectedRegret_eq_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    mdp.optimalPolicy.expectedRegret initialState = 0 := by
  rw [mdp.optimalPolicy.expectedRegret_eq_integral_optimalValueAt_sub_valueAt]
  rw [mdp.optimalPolicy_valueAt_eq_optimalValueAt]
  simp

/--
Route endpoint: expected trajectory regret is exactly the finite occupancy
Bellman-gap sum, is nonnegative for every Markov policy, and vanishes for the
compiled measurable greedy optimal policy.
-/
theorem expectedRegret_eq_occupancyGap_nonneg_and_optimalPolicy_zero
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState] :
    policy.expectedRegret initialState =
        policy.occupancyGapRemaining mdp.horizon le_rfl initialState /\
      0 <= policy.expectedRegret initialState /\
      mdp.optimalPolicy.expectedRegret initialState = 0 := by
  exact ⟨policy.expectedRegret_eq_occupancyGapRemaining initialState,
    policy.expectedRegret_nonneg initialState,
    mdp.optimalPolicy_expectedRegret_eq_zero initialState⟩

end MDP
end FiniteHorizonRL
end BanditRLProof
