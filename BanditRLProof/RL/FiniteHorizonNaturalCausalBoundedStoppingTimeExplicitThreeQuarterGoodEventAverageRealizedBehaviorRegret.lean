import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedStoppingTimeSingleModelEventHighProbabilityAverageRealizedBehaviorRegret

/-!
# Explicit three-quarter bounded-stopping natural causal realized regret

The existing self-consistent schedule assigns two shifted high-power model
confidence shares to every coordinate. This module proves that their complete
finite-prefix budget is at most `1/8`, fixes the global return budget to
`1/8`, and turns the single-model bounded-stopping theorem into a joint bad
event of probability at most `1/4`. Its measurable complement therefore has
real probability at least `3/4` and carries the stopped logarithmic rate.

No optional-stopping identity or independence argument is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace BanditRLProof

/-- A shifted inverse-power prefix with exponent at least six is at most one
sixteenth. This refines the existing inverse-square comparison. -/
theorem sum_range_one_div_natCast_add_two_pow_le_one_div_sixteen
    (rounds exponent : Nat) (hexponent : 6 <= exponent) :
    (Finset.range rounds).sum (fun t =>
      1 / (((t + 2 : Nat) : Real) ^ exponent)) <= 1 / 16 := by
  calc
    (Finset.range rounds).sum (fun t =>
        1 / (((t + 2 : Nat) : Real) ^ exponent)) <=
        (Finset.range rounds).sum (fun t =>
          (1 / 16 : Real) *
            (1 / (((t + 2 : Nat) : Real) ^ 2))) := by
      apply Finset.sum_le_sum
      intro t _ht
      let base : Real := ((t + 2 : Nat) : Real)
      have hbase : (2 : Real) <= base := by
        dsimp [base]
        exact_mod_cast (show 2 <= t + 2 by omega)
      have hbase_pos : 0 < base := lt_of_lt_of_le (by norm_num) hbase
      have hbase_sq : (4 : Real) <= base ^ 2 := by nlinarith
      have hbase_fourth : (16 : Real) <= base ^ 4 := by
        nlinarith [sq_nonneg (base ^ 2 - 4)]
      calc
        1 / (((t + 2 : Nat) : Real) ^ exponent) <=
            1 / (((t + 2 : Nat) : Real) ^ 6) :=
          one_div_pow_le_one_div_pow_of_le
            (by exact_mod_cast (show 1 <= t + 2 by omega)) hexponent
        _ = (1 / base ^ 4) * (1 / base ^ 2) := by
          dsimp [base]
          field_simp [ne_of_gt hbase_pos]
        _ <= (1 / 16 : Real) * (1 / base ^ 2) := by
          exact mul_le_mul_of_nonneg_right
            (one_div_le_one_div_of_le (by norm_num) hbase_fourth)
            (by positivity)
        _ = (1 / 16 : Real) *
            (1 / (((t + 2 : Nat) : Real) ^ 2)) := by
          rfl
    _ = (1 / 16 : Real) *
        (Finset.range rounds).sum (fun t =>
          1 / (((t + 2 : Nat) : Real) ^ 2)) := by
      rw [Finset.mul_sum]
    _ <= (1 / 16 : Real) * 1 :=
      mul_le_mul_of_nonneg_left
        (sum_range_one_div_natCast_add_two_sq_le_one rounds) (by norm_num)
    _ = 1 / 16 := by ring

namespace FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The finite scheduled model budget is the ENNReal image of twice the real
sum of its local confidence schedule. -/
theorem selfConsistentScheduledCausalModelFailureBudget_eq_ofReal_two_mul_sum
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledCausalModelFailureBudget mdp rounds =
      ENNReal.ofReal
        (2 * (Finset.range rounds).sum fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
            mdp t) := by
  have hlocal : forall t : Nat,
      0 <= AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp t := by
    intro t
    rw [selfConsistentScheduledLocalDelta_eq_inv_pow]
    positivity
  rw [selfConsistentScheduledCausalModelFailureBudget_eq_fin_sum]
  calc
    (∑ round : Fin rounds,
        (ENNReal.ofReal
            (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp round) +
          ENNReal.ofReal
            (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp round))) =
        (Finset.range rounds).sum (fun t =>
          ENNReal.ofReal
              (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
                mdp t) +
            ENNReal.ofReal
              (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
                mdp t)) := by
      simpa using
        (Fin.sum_univ_eq_sum_range
          (fun t : Nat =>
            ENNReal.ofReal
                (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
                  mdp t) +
              ENNReal.ofReal
                (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
                  mdp t)) rounds)
    _ = (Finset.range rounds).sum (fun t =>
          ENNReal.ofReal
            (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
                mdp t +
              AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
                mdp t)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [ENNReal.ofReal_add (hlocal t) (hlocal t)]
    _ = ENNReal.ofReal
        ((Finset.range rounds).sum fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp t +
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp t) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro t _ht
      exact add_nonneg (hlocal t) (hlocal t)
    _ = ENNReal.ofReal
        (2 * (Finset.range rounds).sum fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
            mdp t) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every finite prefix of the existing self-consistent model schedule spends
at most one eighth of probability mass across both model-confidence shares. -/
theorem selfConsistentScheduledCausalModelFailureBudget_le_one_eighth
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon) (rounds : Nat) :
    selfConsistentScheduledCausalModelFailureBudget mdp rounds <=
      ENNReal.ofReal (1 / 8 : Real) := by
  rw [selfConsistentScheduledCausalModelFailureBudget_eq_ofReal_two_mul_sum]
  apply ENNReal.ofReal_le_ofReal
  have hsum :=
    BanditRLProof.sum_range_one_div_natCast_add_two_pow_le_one_div_sixteen
      rounds (mdp.horizon + 5) (by omega)
  have hlocal :
      (Finset.range rounds).sum (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
            mdp t) =
        (Finset.range rounds).sum (fun t =>
          1 / (((t + 2 : Nat) : Real) ^ (mdp.horizon + 5))) := by
    apply Finset.sum_congr rfl
    intro t _ht
    exact selfConsistentScheduledLocalDelta_eq_inv_pow mdp t
  rw [hlocal]
  nlinarith

/-- With return budget one eighth, the joint horizon-level model event and all
positive-prefix return events have probability at most one quarter. Its
measurable complement has real probability at least three quarters. -/
theorem
    selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingSingleModelReturnBadEvent_le_one_quarter
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let event :=
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds (1 / 8 : Real)
    MeasurableSet event /\
      source.trajectoryMeasure event <= ENNReal.ofReal (1 / 4 : Real) /\
      (3 / 4 : Real) <= source.trajectoryMeasure.real event.compl := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let event :=
    selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds (1 / 8 : Real)
  have hparent :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingSingleModelReturnBadEvent_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor maxRounds hmaxRounds (1 / 8 : Real)
            (by norm_num) (by norm_num)
  have heventMeasurable : MeasurableSet event := by
    simpa [event] using hparent.1
  have hmodel :
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds <=
        ENNReal.ofReal (1 / 8 : Real) :=
    selfConsistentScheduledCausalModelFailureBudget_le_one_eighth
      mdp hhorizon maxRounds
  have hbudget :
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
          ENNReal.ofReal (1 / 8 : Real) <=
        ENNReal.ofReal (1 / 4 : Real) := by
    calc
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
          ENNReal.ofReal (1 / 8 : Real) <=
          ENNReal.ofReal (1 / 8 : Real) +
            ENNReal.ofReal (1 / 8 : Real) :=
        add_le_add hmodel (le_refl _)
      _ = ENNReal.ofReal ((1 / 8 : Real) + (1 / 8 : Real)) := by
        rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
      _ = ENNReal.ofReal (1 / 4 : Real) := by norm_num
  have heventTail :
      source.trajectoryMeasure event <= ENNReal.ofReal (1 / 4 : Real) := by
    have hraw :
        source.trajectoryMeasure event <=
          selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
            ENNReal.ofReal (1 / 8 : Real) := by
      simpa [source, event] using hparent.2
    exact hraw.trans hbudget
  have heventTailReal : source.trajectoryMeasure.real event <= 1 / 4 := by
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    exact heventTail
  have hgoodMass :
      (3 / 4 : Real) <= source.trajectoryMeasure.real event.compl := by
    change (3 / 4 : Real) <= source.trajectoryMeasure.real (eventᶜ)
    rw [MeasureTheory.probReal_compl_eq_one_sub heventMeasurable]
    linarith
  exact ⟨heventMeasurable, heventTail, hgoodMass⟩

/-
Terminal explicit-confidence route. The good event is the complement of the
same single-model/return event used by the compiled bounded-stopping parent.
-/
theorem
    selfConsistentScheduledCausalSource_boundedStoppingTimeExplicitThreeQuarterGoodEventAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (htau : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) tau)
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat)) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let returnDeltaAt := fun _ : Nat =>
      selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
        maxRounds (1 / 8 : Real)
    let stoppedViolation :=
      selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau
    let event :=
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds (1 / 8 : Real)
    let goodEvent := event.compl
    MeasurableSet[
        selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            maxRounds] stoppedViolation /\
      MeasurableSet event /\
      MeasurableSet goodEvent /\
      stoppedViolation ⊆ event /\
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds <=
        ENNReal.ofReal (1 / 8 : Real) /\
      source.trajectoryMeasure event <= ENNReal.ofReal (1 / 4 : Real) /\
      source.trajectoryMeasure stoppedViolation <=
        ENNReal.ofReal (1 / 4 : Real) /\
      (3 / 4 : Real) <= source.trajectoryMeasure.real goodEvent /\
      forall trajectory, trajectory ∈ goodEvent ->
        selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor tau trajectory <=
          selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor returnDeltaAt tau trajectory := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let returnDeltaAt := fun _ : Nat =>
    selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
      maxRounds (1 / 8 : Real)
  let stoppedViolation :=
    selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor returnDeltaAt tau
  let event :=
    selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds (1 / 8 : Real)
  have hparent :=
    selfConsistentScheduledCausalSource_boundedStoppingTimeSingleModelEventHighProbabilityAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor tau htau maxRounds hmaxRounds htau_pos htau_le
            (1 / 8 : Real) (by norm_num) (by norm_num)
  rcases hparent with
    ⟨hstoppedMeasurable, heventMeasurable, hsubset, _heventRaw,
      hstoppedRaw, _hsubunit, hpathwise⟩
  have hmodel :
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds <=
        ENNReal.ofReal (1 / 8 : Real) :=
    selfConsistentScheduledCausalModelFailureBudget_le_one_eighth
      mdp hhorizon maxRounds
  have hbudget :
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
          ENNReal.ofReal (1 / 8 : Real) <=
        ENNReal.ofReal (1 / 4 : Real) := by
    calc
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
          ENNReal.ofReal (1 / 8 : Real) <=
          ENNReal.ofReal (1 / 8 : Real) +
            ENNReal.ofReal (1 / 8 : Real) :=
        add_le_add hmodel (le_refl _)
      _ = ENNReal.ofReal ((1 / 8 : Real) + (1 / 8 : Real)) := by
        rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
      _ = ENNReal.ofReal (1 / 4 : Real) := by norm_num
  have hgood :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingSingleModelReturnBadEvent_le_one_quarter
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor maxRounds hmaxRounds
  have heventQuarter :
      source.trajectoryMeasure event <= ENNReal.ofReal (1 / 4 : Real) := by
    simpa [source, event] using hgood.2.1
  have hstoppedQuarter :
      source.trajectoryMeasure stoppedViolation <=
        ENNReal.ofReal (1 / 4 : Real) := by
    have hraw :
        source.trajectoryMeasure stoppedViolation <=
          selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
            ENNReal.ofReal (1 / 8 : Real) := by
      simpa [source, stoppedViolation, returnDeltaAt] using hstoppedRaw
    exact hraw.trans hbudget
  have hgoodMass :
      (3 / 4 : Real) <= source.trajectoryMeasure.real event.compl := by
    simpa [source, event] using hgood.2.2
  refine ⟨?_, ?_, ?_, ?_, hmodel, heventQuarter, hstoppedQuarter,
    hgoodMass, ?_⟩
  · change MeasurableSet[
      selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          maxRounds] stoppedViolation
    exact hstoppedMeasurable
  · change MeasurableSet event
    exact heventMeasurable
  · change MeasurableSet event.compl
    exact heventMeasurable.compl
  · change stoppedViolation ⊆ event
    exact hsubset
  · intro trajectory htrajectory
    have hnotEvent : trajectory ∉ event := by
      exact htrajectory
    exact hpathwise trajectory hnotEvent

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end FiniteHorizonRL
end BanditRLProof
