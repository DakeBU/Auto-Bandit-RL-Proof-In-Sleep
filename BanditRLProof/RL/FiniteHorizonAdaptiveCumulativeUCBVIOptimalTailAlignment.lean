import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVISimultaneousConfidence

/-! Exact affine transport from the normalized generated probe to `V*`. -/

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

/-- Integrating the normalized optimal-tail probe against two probability
measures and subtracting transports exactly back to the `V*` difference. -/
theorem integral_optimalValue_sub_eq_two_mul_horizon_mul_integral_probe_sub
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    (∫ nextState,
        mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt) nextState
          ∂summary.aggregateEmpiricalTransitionKernel defaultState (state, action)) -
      mdp.transitionValue
        (mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt))
        state action =
      2 * (mdp.horizon : Real) *
        ((∫ nextState, mdp.optimalTailProbe stage nextState
            ∂summary.aggregateEmpiricalTransitionKernel defaultState (state, action)) -
          mdp.transitionValue (mdp.optimalTailProbe stage) state action) := by
  let empirical := summary.aggregateEmpiricalTransitionKernel defaultState
      (state, action)
  let truth := mdp.transition (state, action)
  let value := mdp.optimalValueAt (stage + 1)
      (Nat.succ_le_of_lt stage.isLt)
  let probe := mdp.optimalTailProbe stage
  let scale : Real := 2 * (mdp.horizon : Real)
  have hhorizon : (mdp.horizon : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.pos_of_ne_zero (by
      intro hzero
      have : stage.val < 0 := by simpa [hzero] using stage.isLt
      omega))
  have hpoint : ∀ nextState, value nextState =
      scale * probe nextState - (mdp.horizon : Real) := by
    intro nextState
    simp only [value, scale, probe, MDP.optimalTailProbe]
    field_simp
    ring
  letI : IsProbabilityMeasure empirical :=
    (summary.aggregateEmpiricalTransitionKernel_isMarkov defaultState).isProbabilityMeasure
      (state, action)
  letI : IsProbabilityMeasure truth := mdp.transition_isMarkov.isProbabilityMeasure
      (state, action)
  have hprobeMeasurable : Measurable probe := measurable_of_finite _
  have hprobeEmpirical : Integrable probe empirical :=
    integrable_of_fintype _ _ hprobeMeasurable
  have hprobeTruth : Integrable probe truth :=
    integrable_of_fintype _ _ hprobeMeasurable
  have hempirical :
      (∫ nextState, value nextState ∂empirical) =
        scale * (∫ nextState, probe nextState ∂empirical) -
          (mdp.horizon : Real) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_sub]
    · rw [integral_const, measureReal_univ_eq_one, one_smul]
      rw [integral_const_mul scale probe]
    · exact hprobeEmpirical.const_mul _
    · exact integrable_const _
  have htruth :
      (∫ nextState, value nextState ∂truth) =
        scale * (∫ nextState, probe nextState ∂truth) -
          (mdp.horizon : Real) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_sub]
    · rw [integral_const, measureReal_univ_eq_one, one_smul]
      rw [integral_const_mul scale probe]
    · exact hprobeTruth.const_mul _
    · exact integrable_const _
  change (∫ nextState, value nextState ∂empirical) -
      (∫ nextState, value nextState ∂truth) =
    scale * ((∫ nextState, probe nextState ∂empirical) -
      (∫ nextState, probe nextState ∂truth))
  rw [hempirical, htruth]
  ring

namespace AdaptiveEpisodeBatchSource

/-- Outside the proved joint event, the empirical transition kernel consumed
by the planner has the sharp `V*` projection error at every peeled positive
actual count.  No confidence statement is supplied by the caller. -/
theorem abs_empiricalTransition_optimalValue_sub_lt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {logBudget : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (htrajectory : trajectory ∉
      simultaneousTransitionFailureEvent source episodes logBudget)
    (defaultState : State) (index : OptimalTailIndex mdp episodes)
    (hactual : adaptiveCumulativeAggregateVisitCountAt trajectory index.round
        index.state index.action = index.count + 1) :
    |(∫ nextState,
          mdp.optimalValueAt (index.stage + 1)
              (Nat.succ_le_of_lt index.stage.isLt) nextState
            ∂TransitionCountSummary.aggregateEmpiricalTransitionKernel
              (adaptiveCumulativeEmpiricalModelStateAt trajectory index.round).1
              defaultState (index.state, index.action)) -
        mdp.transitionValue
          (mdp.optimalValueAt (index.stage + 1)
            (Nat.succ_le_of_lt index.stage.isLt))
          index.state index.action| <
      2 * (mdp.horizon : Real) * logBudget /
        Real.sqrt (index.count + 1 : Nat) := by
  let summary := (adaptiveCumulativeEmpiricalModelStateAt trajectory index.round).1
  let count : Real := (index.count + 1 : Nat)
  let probeDifference : Real :=
    (∫ nextState, mdp.optimalTailProbe index.stage nextState
        ∂summary.aggregateEmpiricalTransitionKernel defaultState
          (index.state, index.action)) -
      mdp.transitionValue (mdp.optimalTailProbe index.stage)
        index.state index.action
  have hcountPosNat : 0 < adaptiveCumulativeAggregateVisitCountAt trajectory
      index.round index.state index.action := by
    rw [hactual]
    exact Nat.succ_pos _
  have hvisitSum :
      (∑ i ∈ Finset.range (index.round + 1),
          source.aggregateVisitIncrement index.state index.action i trajectory) =
        (index.count + 1 : Nat) := by
    rw [source.sum_aggregateVisitIncrement_eq_prefixAggregateVisitCount]
    exact_mod_cast hactual
  have hresidual :=
    abs_optimalTailResidual_lt_of_not_mem_simultaneousTransitionFailureEvent
      source htrajectory index hvisitSum
  have halignment :=
    source.aggregateTransitionFunctionalResidual_eq_count_mul_transitionValue_sub
      trajectory index.round defaultState (mdp.optimalTailProbe index.stage)
      index.state index.action hcountPosNat
  have hresidual' : |count * probeDifference| <
      logBudget * Real.sqrt count := by
    rw [halignment, hactual] at hresidual
    simpa [count, probeDifference, summary] using hresidual
  have hcountPos : 0 < count := by
    change 0 < ((index.count + 1 : Nat) : Real)
    positivity
  have hsqrtPos : 0 < Real.sqrt count := Real.sqrt_pos.2 hcountPos
  have hsqrtSq : Real.sqrt count ^ 2 = count := Real.sq_sqrt hcountPos.le
  have hsqrtMul : Real.sqrt count * Real.sqrt count = count := by
    simpa [pow_two] using hsqrtSq
  have hprobe : |probeDifference| < logBudget / Real.sqrt count := by
    rw [abs_mul, abs_of_pos hcountPos] at hresidual'
    apply (lt_div_iff₀ hsqrtPos).2
    refine lt_of_mul_lt_mul_right (a := Real.sqrt count) ?_ hsqrtPos.le
    calc
      |probeDifference| * Real.sqrt count * Real.sqrt count =
          |probeDifference| * count := by rw [mul_assoc, hsqrtMul]
      _ = count * |probeDifference| := by ring
      _ < logBudget * Real.sqrt count := hresidual'
  have haffine :=
    integral_optimalValue_sub_eq_two_mul_horizon_mul_integral_probe_sub
      mdp summary defaultState index.stage index.state index.action
  have hhorizon : 0 < (mdp.horizon : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro hzero
      have : index.stage.val < 0 := by simpa [hzero] using index.stage.isLt
      omega)
  rw [haffine, abs_mul, abs_of_pos (mul_pos (by norm_num) hhorizon)]
  simpa [count, probeDifference, summary, mul_div_assoc] using
    (mul_lt_mul_of_pos_left hprobe (mul_pos (by norm_num) hhorizon))

end AdaptiveEpisodeBatchSource

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
