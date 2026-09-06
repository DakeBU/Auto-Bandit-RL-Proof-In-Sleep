import BanditRLProof.RL.FiniteHorizonOccupancyRegret

/-!
# Finite-horizon optimistic Bellman certificates

This module isolates the deterministic dynamic-programming interface needed by
optimistic finite-horizon RL.  A certificate supplies upper values with zero
terminal value and a one-step upper Bellman inequality.  Backward induction
turns that local contract into global optimism.  For any Markov policy, the
upper-value minus policy-value difference is then exactly a recursive sum of
Bellman residuals under the true policy-induced state laws.  A pointwise bonus
bound on those residuals yields a finite-episode expected-regret bound.
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

namespace MDP

/-- The finite-action optimal Bellman operator is monotone in its continuation value. -/
theorem optimalBellman_mono
    (mdp : MDP State Action) {left right : State -> Real}
    (hle : forall state, left state <= right state) (state : State) :
    mdp.optimalBellman left state <= mdp.optimalBellman right state := by
  calc
    mdp.optimalBellman left state =
        mdp.bellmanQ left state (mdp.optimalAction left state) := rfl
    _ <= mdp.bellmanQ right state (mdp.optimalAction left state) :=
      mdp.bellmanQ_mono hle state (mdp.optimalAction left state)
    _ <= mdp.optimalBellman right state :=
      mdp.bellmanQ_le_optimalBellman right state (mdp.optimalAction left state)

/--
An upper-value plan whose terminal value is zero and whose successor surface
dominates one true optimal Bellman backup of its tail surface.
-/
structure OptimisticBellmanCertificate (mdp : MDP State Action) where
  upperValueRemaining :
    (remaining : Nat) -> remaining <= mdp.horizon -> State -> Real
  upperValueRemaining_zero :
    upperValueRemaining 0 (Nat.zero_le mdp.horizon) = fun _ => 0
  optimalBellman_le_upperValueRemaining_succ :
    forall (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon) (state : State),
      mdp.optimalBellman
          (upperValueRemaining remaining (by omega)) state <=
        upperValueRemaining (remaining + 1) hremaining state

/-- The true optimal value itself is the canonical exact optimistic certificate. -/
noncomputable def optimalBellmanCertificate (mdp : MDP State Action) :
    OptimisticBellmanCertificate mdp where
  upperValueRemaining := mdp.optimalValueRemaining
  upperValueRemaining_zero := rfl
  optimalBellman_le_upperValueRemaining_succ := by
    intro remaining hremaining state
    rw [optimalValueRemaining]

namespace OptimisticBellmanCertificate

/-- Every upper-value surface is measurable on the finite discrete state space. -/
theorem measurable_upperValueRemaining
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    Measurable (certificate.upperValueRemaining remaining hremaining) :=
  measurable_of_finite _

/-- Local Bellman optimism implies the upper values dominate the true optimal values. -/
theorem optimalValueRemaining_le_upperValueRemaining
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) :
    mdp.optimalValueRemaining remaining hremaining state <=
      certificate.upperValueRemaining remaining hremaining state := by
  induction remaining generalizing state with
  | zero =>
      rw [MDP.optimalValueRemaining, certificate.upperValueRemaining_zero]
  | succ remaining ih =>
      rw [MDP.optimalValueRemaining]
      exact
        (mdp.optimalBellman_mono
          (fun nextState => ih (by omega) nextState) state).trans
        (certificate.optimalBellman_le_upperValueRemaining_succ
          remaining hremaining state)

end OptimisticBellmanCertificate
end MDP

namespace MarkovPolicy

/--
Recursive occupancy sum for a remaining-horizon-indexed stage cost.  At a
successor step, cost index `remaining` is chronological stage
`horizon - (remaining + 1)`.
-/
noncomputable def occupancySumRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (cost : (remaining : Nat) ->
      remaining + 1 <= mdp.horizon -> State -> Real) :
    (remaining : Nat) -> remaining <= mdp.horizon -> Measure State -> Real
  | 0, _, _ => 0
  | remaining + 1, hremaining, mu =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      (∫ state, cost remaining hremaining state ∂mu) +
        policy.occupancySumRemaining cost remaining (by omega)
          (policy.inducedStateKernel stage ∘ₘ mu)

omit [MeasurableSingletonClass State] [Nonempty Action] in
/-- Successor equation for a generic recursive occupancy sum. -/
theorem occupancySumRemaining_succ
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (cost : (remaining : Nat) ->
      remaining + 1 <= mdp.horizon -> State -> Real)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (mu : Measure State) :
    policy.occupancySumRemaining cost (remaining + 1) hremaining mu =
      (∫ state, cost remaining hremaining state ∂mu) +
        policy.occupancySumRemaining cost remaining (by omega)
          (policy.inducedStateKernel
            ⟨mdp.horizon - (remaining + 1), by omega⟩ ∘ₘ mu) := by
  rw [occupancySumRemaining]

omit [Nonempty Action] in
/-- Pointwise domination of stage costs lifts to domination of their occupancy sums. -/
theorem occupancySumRemaining_mono
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    {left right : (remaining : Nat) ->
      remaining + 1 <= mdp.horizon -> State -> Real}
    (hle : forall (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon) (state : State),
      left remaining hremaining state <= right remaining hremaining state)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    policy.occupancySumRemaining left remaining hremaining mu <=
      policy.occupancySumRemaining right remaining hremaining mu := by
  induction remaining generalizing mu with
  | zero =>
      simp [occupancySumRemaining]
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let nextMu : Measure State := policy.inducedStateKernel stage ∘ₘ mu
      letI : IsProbabilityMeasure nextMu := by
        dsimp [nextMu]
        infer_instance
      rw [occupancySumRemaining]
      apply add_le_add
      · apply integral_mono
        · exact integrable_of_fintype _ _ (measurable_of_finite _)
        · exact integrable_of_fintype _ _ (measurable_of_finite _)
        · exact fun state => hle remaining hremaining state
      · exact ih (by omega) nextMu

end MarkovPolicy

namespace MDP.OptimisticBellmanCertificate

/-- Policy Bellman residual of an optimistic upper-value plan. -/
noncomputable def policyBellmanResidual
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) : Real :=
  certificate.upperValueRemaining (remaining + 1) hremaining state -
    policy.bellman ⟨mdp.horizon - (remaining + 1), by omega⟩
      (certificate.upperValueRemaining remaining (by omega)) state

/-- The optimistic policy Bellman residual is measurable. -/
theorem measurable_policyBellmanResidual
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) :
    Measurable (certificate.policyBellmanResidual policy remaining hremaining) := by
  exact (certificate.measurable_upperValueRemaining (remaining + 1) hremaining).sub
    (policy.measurable_bellman _
      (certificate.measurable_upperValueRemaining remaining (by omega)))

/-- Every policy Bellman residual of an optimistic certificate is nonnegative. -/
theorem policyBellmanResidual_nonneg
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    0 <= certificate.policyBellmanResidual policy remaining hremaining state := by
  unfold policyBellmanResidual
  apply sub_nonneg.mpr
  exact
    (policy.bellman_le_optimalBellman
      ⟨mdp.horizon - (remaining + 1), by omega⟩
      (certificate.upperValueRemaining remaining (by omega)) state).trans
    (certificate.optimalBellman_le_upperValueRemaining_succ
      remaining hremaining state)

/-- Recursive true-occupancy sum of the certificate's policy Bellman residuals. -/
noncomputable def residualOccupancyRemaining
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon) (mu : Measure State) : Real :=
  policy.occupancySumRemaining
    (certificate.policyBellmanResidual policy) remaining hremaining mu

/--
The residual occupancy sum is exactly the integrated difference between the
certificate upper value and the supplied policy value.
-/
theorem residualOccupancyRemaining_eq_integral_upperValueRemaining_sub_valueRemaining
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    certificate.residualOccupancyRemaining policy remaining hremaining mu =
      ∫ state, certificate.upperValueRemaining remaining hremaining state -
        policy.valueRemaining remaining hremaining state ∂mu := by
  induction remaining generalizing mu with
  | zero =>
      simp [residualOccupancyRemaining, MarkovPolicy.occupancySumRemaining,
        certificate.upperValueRemaining_zero, MarkovPolicy.valueRemaining]
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let nextMu : Measure State := policy.inducedStateKernel stage ∘ₘ mu
      letI : IsProbabilityMeasure nextMu := by
        dsimp [nextMu]
        infer_instance
      unfold residualOccupancyRemaining
      rw [MarkovPolicy.occupancySumRemaining]
      change
        (∫ state,
            certificate.policyBellmanResidual policy remaining hremaining state ∂mu) +
          certificate.residualOccupancyRemaining policy remaining (by omega) nextMu = _
      rw [ih (by omega) nextMu]
      rw [policy.integral_sub_comp_inducedStateKernel_eq_integral_bellman_sub
        stage
        (certificate.upperValueRemaining remaining (by omega))
        (policy.valueRemaining remaining (by omega)) mu]
      rw [MarkovPolicy.valueRemaining]
      unfold policyBellmanResidual
      have hfirst : Integrable
          (fun state =>
            certificate.upperValueRemaining (remaining + 1) hremaining state -
              policy.bellman stage
                (certificate.upperValueRemaining remaining (by omega)) state) mu :=
        integrable_of_fintype _ _ (measurable_of_finite _)
      have hsecond : Integrable
          (fun state =>
            policy.bellman stage
                (certificate.upperValueRemaining remaining (by omega)) state -
              policy.bellman stage
                (policy.valueRemaining remaining (by omega)) state) mu :=
        integrable_of_fintype _ _ (measurable_of_finite _)
      rw [← integral_add hfirst hsecond]
      apply integral_congr_ae
      filter_upwards [] with state
      ring

/-- For the canonical exact certificate, residual occupancy is the previously compiled optimality
gap occupancy sum. -/
theorem optimalBellmanCertificate_residualOccupancyRemaining_eq_occupancyGapRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    mdp.optimalBellmanCertificate.residualOccupancyRemaining
        policy remaining hremaining mu =
      policy.occupancyGapRemaining remaining hremaining mu := by
  rw [mdp.optimalBellmanCertificate.residualOccupancyRemaining_eq_integral_upperValueRemaining_sub_valueRemaining]
  rw [policy.occupancyGapRemaining_eq_integral_optimalValueRemaining_sub_valueRemaining]
  rfl

/-- The residual occupancy sum is nonnegative. -/
theorem residualOccupancyRemaining_nonneg
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    0 <= certificate.residualOccupancyRemaining policy remaining hremaining mu := by
  rw [certificate.residualOccupancyRemaining_eq_integral_upperValueRemaining_sub_valueRemaining]
  apply integral_nonneg
  intro state
  apply sub_nonneg.mpr
  exact
    (policy.valueRemaining_le_optimalValueRemaining remaining hremaining state).trans
    (certificate.optimalValueRemaining_le_upperValueRemaining
      remaining hremaining state)

/-- Single-episode expected regret is bounded by the optimistic residual occupancy sum. -/
theorem expectedRegret_le_residualOccupancyRemaining
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    policy.expectedRegret initialState <=
      certificate.residualOccupancyRemaining
        policy mdp.horizon le_rfl initialState := by
  rw [policy.expectedRegret_eq_integral_optimalValueAt_sub_valueAt]
  rw [certificate.residualOccupancyRemaining_eq_integral_upperValueRemaining_sub_valueRemaining]
  apply integral_mono
  · exact integrable_of_fintype _ _ (measurable_of_finite _)
  · exact integrable_of_fintype _ _ (measurable_of_finite _)
  · intro state
    exact sub_le_sub_right
      (certificate.optimalValueRemaining_le_upperValueRemaining
        mdp.horizon le_rfl state)
      (policy.valueAt 0 (Nat.zero_le mdp.horizon) state)

/-- A pointwise bonus bound on Bellman residuals bounds the residual occupancy sum. -/
theorem residualOccupancyRemaining_le_occupancySumRemaining
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp)
    (bonus : (remaining : Nat) ->
      remaining + 1 <= mdp.horizon -> State -> Real)
    (hbonus : forall (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon) (state : State),
      certificate.policyBellmanResidual policy remaining hremaining state <=
        bonus remaining hremaining state)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    certificate.residualOccupancyRemaining policy remaining hremaining mu <=
      policy.occupancySumRemaining bonus remaining hremaining mu := by
  unfold residualOccupancyRemaining
  exact policy.occupancySumRemaining_mono hbonus remaining hremaining mu

/--
Route endpoint: local true-Bellman optimism induces global value optimism;
single-episode expected regret is bounded by the true-occupancy residual sum;
and any pointwise bonus dominating those residuals bounds regret.
-/
theorem expectedRegret_le_residual_le_occupancyBonusRemaining
    {mdp : MDP State Action} (certificate : OptimisticBellmanCertificate mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (bonus : (remaining : Nat) ->
      remaining + 1 <= mdp.horizon -> State -> Real)
    (hbonus : forall (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon) (state : State),
      certificate.policyBellmanResidual policy remaining hremaining state <=
        bonus remaining hremaining state) :
    0 <= certificate.residualOccupancyRemaining
        policy mdp.horizon le_rfl initialState /\
      policy.expectedRegret initialState <=
        certificate.residualOccupancyRemaining
          policy mdp.horizon le_rfl initialState /\
      certificate.residualOccupancyRemaining
          policy mdp.horizon le_rfl initialState <=
        policy.occupancySumRemaining bonus mdp.horizon le_rfl initialState /\
      policy.expectedRegret initialState <=
        policy.occupancySumRemaining bonus mdp.horizon le_rfl initialState := by
  have hregret := certificate.expectedRegret_le_residualOccupancyRemaining
    policy initialState
  have hresidual := certificate.residualOccupancyRemaining_le_occupancySumRemaining
    policy bonus hbonus mdp.horizon le_rfl initialState
  exact ⟨certificate.residualOccupancyRemaining_nonneg
      policy mdp.horizon le_rfl initialState,
    hregret, hresidual, hregret.trans hresidual⟩

end MDP.OptimisticBellmanCertificate
end FiniteHorizonRL
end BanditRLProof
