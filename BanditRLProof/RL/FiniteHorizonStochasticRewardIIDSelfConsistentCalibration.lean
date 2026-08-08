import BanditRLProof.RL.FiniteHorizonStochasticRewardIIDExplicitCalibration

/-!
# Self-consistent stochastic transition calibration

The half-contraction calibration uses the coarse fixed point
`transitionBudget = rewardBound + 2 * rewardBudget`.  Here the actual
contraction factor `q < 1` is retained and the fixed point is solved exactly,
so the transition budget shrinks with `q`.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof.FiniteHorizonRL

/-- Exact nonnegative fixed-point budget for `q * (base + budget) <= budget`. -/
noncomputable def selfConsistentTransitionBudget
    (q base : Real) : Real :=
  q * base / (1 - q)

/-- The fixed-point budget is nonnegative when `0 <= q < 1` and `base >= 0`. -/
theorem selfConsistentTransitionBudget_nonneg
    {q base : Real} (hq_nonneg : 0 <= q) (hq : q < 1)
    (hbase : 0 <= base) :
    0 <= selfConsistentTransitionBudget q base := by
  unfold selfConsistentTransitionBudget
  exact div_nonneg (mul_nonneg hq_nonneg hbase) (sub_nonneg.mpr hq.le)

/-- The chosen budget solves the transition-envelope fixed point exactly. -/
theorem selfConsistentTransitionBudget_fixedPoint
    {q base : Real} (hq : q < 1) :
    q * (base + selfConsistentTransitionBudget q base) =
      selfConsistentTransitionBudget q base := by
  have hdenom : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  unfold selfConsistentTransitionBudget
  field_simp [hdenom]
  ring

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/-- The exact common-floor transition contraction factor. -/
noncomputable def uniformFloorStochasticTransitionContraction
    (mdp : MDP State Action) (episodes : Nat)
    (countDelta visitFloor : Real) : Real :=
  (Fintype.card State : Real) *
    uniformFloorTransitionCoordinateRadius mdp episodes countDelta visitFloor *
    (mdp.horizon : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The common-floor contraction factor is nonnegative under the count margin. -/
theorem uniformFloorStochasticTransitionContraction_nonneg
    {mdp : MDP State Action} {episodes : Nat}
    {countDelta visitFloor : Real}
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      (episodes : Real) * visitFloor) :
    0 <= uniformFloorStochasticTransitionContraction
      mdp episodes countDelta visitFloor := by
  unfold uniformFloorStochasticTransitionContraction
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (uniformFloorTransitionCoordinateRadius_nonneg hmargin))
    (Nat.cast_nonneg _)

/-- Shrinking transition budget obtained from the exact contraction factor. -/
noncomputable def uniformFloorStochasticSelfConsistentTransitionBudget
    (mdp : MDP State Action) (episodes : Nat)
    (countDelta visitFloor rewardBound rewardBudget : Real) : Real :=
  selfConsistentTransitionBudget
    (uniformFloorStochasticTransitionContraction
      mdp episodes countDelta visitFloor)
    (rewardBound + 2 * rewardBudget)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The shrinking transition budget is nonnegative under `q < 1`. -/
theorem uniformFloorStochasticSelfConsistentTransitionBudget_nonneg
    {mdp : MDP State Action} {episodes : Nat}
    {countDelta visitFloor rewardBound rewardBudget : Real}
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      (episodes : Real) * visitFloor)
    (hrewardBound_nonneg : 0 <= rewardBound)
    (hrewardBudget_nonneg : 0 <= rewardBudget)
    (hq : uniformFloorStochasticTransitionContraction
      mdp episodes countDelta visitFloor < 1) :
    0 <= uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
      countDelta visitFloor rewardBound rewardBudget := by
  unfold uniformFloorStochasticSelfConsistentTransitionBudget
  exact selfConsistentTransitionBudget_nonneg
    (uniformFloorStochasticTransitionContraction_nonneg hmargin) hq
    (add_nonneg hrewardBound_nonneg
      (mul_nonneg (by norm_num) hrewardBudget_nonneg))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The common-floor shrinking budget satisfies the exact envelope identity. -/
theorem uniformFloorStochasticSelfConsistentTransitionBudget_fixedPoint
    {mdp : MDP State Action} {episodes : Nat}
    {countDelta visitFloor rewardBound rewardBudget : Real}
    (hq : uniformFloorStochasticTransitionContraction
      mdp episodes countDelta visitFloor < 1) :
    uniformFloorStochasticTransitionContraction
          mdp episodes countDelta visitFloor *
        (rewardBound + 2 * rewardBudget +
          uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
            countDelta visitFloor rewardBound rewardBudget) =
      uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
        countDelta visitFloor rewardBound rewardBudget := by
  unfold uniformFloorStochasticSelfConsistentTransitionBudget
  exact selfConsistentTransitionBudget_fixedPoint hq

namespace MarkovPolicy

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/--
The exact `q < 1` fixed point covers every transition-radius/value-envelope
sum with a budget that shrinks as `q` tends to zero.
-/
theorem stochasticTransitionCover_of_uniformExpectedCountFloor_selfConsistent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta visitFloor rewardBound : Real)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      (episodes : Real) * visitFloor)
    (hcountFloor : forall coordinate : VisitCoordinate mdp,
      (episodes : Real) * visitFloor <=
        coordinate.expectedCount policy initialState episodes)
    (hrewardBound_nonneg : 0 <= rewardBound)
    (hq : uniformFloorStochasticTransitionContraction mdp episodes countDelta
      visitFloor < 1) :
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
        countDelta visitFloor rewardBound rewardBudget
    forall (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius initialState episodes
              countDelta (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            stochasticEmpiricalFiniteBatchValueEnvelope rewardBound
              rewardBudget transitionBudget remaining) <=
        transitionBudget := by
  dsimp only
  intro remaining hremaining state action
  let rewardBudget :=
    uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
      countDelta rewardDelta visitFloor
  let transitionBudget :=
    uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
      countDelta visitFloor rewardBound rewardBudget
  let q := uniformFloorStochasticTransitionContraction
    mdp episodes countDelta visitFloor
  have hrewardBudget_nonneg : 0 <= rewardBudget :=
    uniformFloorStochasticRewardCoordinateRadius_nonneg hmargin
  have htransitionBudget_nonneg : 0 <= transitionBudget := by
    exact uniformFloorStochasticSelfConsistentTransitionBudget_nonneg
      hmargin hrewardBound_nonneg hrewardBudget_nonneg hq
  have huniform_nonneg :
      0 <= uniformFloorTransitionCoordinateRadius mdp episodes countDelta
        visitFloor :=
    uniformFloorTransitionCoordinateRadius_nonneg hmargin
  have henvelope_nonneg :
      0 <= stochasticEmpiricalFiniteBatchValueEnvelope rewardBound rewardBudget
        transitionBudget remaining := by
    unfold stochasticEmpiricalFiniteBatchValueEnvelope
    positivity
  have hremaining_le : (remaining : Real) <= (mdp.horizon : Real) := by
    exact_mod_cast (show remaining <= mdp.horizon by omega)
  have hcoefficient :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes countDelta
            visitFloor *
          (remaining : Real) <=
        q := by
    dsimp [q, uniformFloorStochasticTransitionContraction]
    exact mul_le_mul_of_nonneg_left hremaining_le
      (mul_nonneg (Nat.cast_nonneg _) huniform_nonneg)
  have hbase_nonneg :
      0 <= rewardBound + 2 * rewardBudget + transitionBudget := by
    positivity
  change
    (∑ nextState,
        policy.expectedCountTransitionCoordinateRadius initialState episodes
            countDelta (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          stochasticEmpiricalFiniteBatchValueEnvelope rewardBound rewardBudget
            transitionBudget remaining) <=
      transitionBudget
  calc
    (∑ nextState,
        policy.expectedCountTransitionCoordinateRadius initialState episodes
            countDelta (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          stochasticEmpiricalFiniteBatchValueEnvelope rewardBound rewardBudget
            transitionBudget remaining) <=
        ∑ _nextState : State,
          uniformFloorTransitionCoordinateRadius mdp episodes countDelta
              visitFloor *
            stochasticEmpiricalFiniteBatchValueEnvelope rewardBound rewardBudget
              transitionBudget remaining := by
      apply Finset.sum_le_sum
      intro nextState _hnextState
      exact mul_le_mul_of_nonneg_right
        (policy.expectedCountTransitionCoordinateRadius_le_uniformFloor
          initialState episodes countDelta visitFloor hmargin hcountFloor
          (mdp.decisionStageRemaining remaining hremaining)
          state action nextState)
        henvelope_nonneg
    _ = ((Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes countDelta
            visitFloor *
          (remaining : Real)) *
        (rewardBound + 2 * rewardBudget + transitionBudget) := by
      simp [stochasticEmpiricalFiniteBatchValueEnvelope]
      ring
    _ <= q * (rewardBound + 2 * rewardBudget + transitionBudget) :=
      mul_le_mul_of_nonneg_right hcoefficient hbase_nonneg
    _ = transitionBudget := by
      simpa [q, transitionBudget] using
        (uniformFloorStochasticSelfConsistentTransitionBudget_fixedPoint
          (mdp := mdp) (episodes := episodes) (countDelta := countDelta)
          (visitFloor := visitFloor) (rewardBound := rewardBound)
          (rewardBudget := rewardBudget) hq)

/-- Fixed-policy all-coordinate confidence under the shrinking transition budget. -/
theorem iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_uniformExpectedCountFloor_selfConsistent
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action}
    (source : mdp.MeanCompatibleRewardKernel)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1)
    (defaultState : State) (rewardBound visitFloor : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      (episodes : Real) * visitFloor)
    (hcountFloor : forall coordinate : VisitCoordinate mdp,
      (episodes : Real) * visitFloor <=
        coordinate.expectedCount policy initialState episodes)
    (hq : uniformFloorStochasticTransitionContraction mdp episodes countDelta
      visitFloor < 1) :
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
        countDelta visitFloor rewardBound rewardBudget
    let event := source.stochasticAllCoordinateEmpiricalModelBadEvent policy
      initialState episodes varianceProxy countDelta rewardDelta
    MeasurableSet event /\
      (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
          event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta /\
      forall trajectories, trajectories ∉ event ->
        let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
          episodes (mdp.sampledEpisodeBatchOfStochasticTrajectories
            episodes trajectories) defaultState rewardBudget transitionBudget
        (forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              model.plan.upperValueRemaining mdp.horizon le_rfl state) /\
          model.plan.optimisticPolicy.expectedRegret initialState <=
            model.plan.optimisticPolicy.occupancySumRemaining
              (fun remaining hremaining state =>
                2 * model.plan.selectedRadiusRemaining
                  remaining hremaining state)
              mdp.horizon le_rfl initialState := by
  dsimp only
  have hrewardBound_nonneg : 0 <= rewardBound := by
    let action : Action := Classical.choice inferInstance
    exact (abs_nonneg (mdp.reward defaultState action)).trans
      (hrewardBound defaultState action)
  have hrewardBudget_nonneg :
      0 <= uniformFloorStochasticRewardCoordinateRadius mdp episodes
        varianceProxy countDelta rewardDelta visitFloor :=
    uniformFloorStochasticRewardCoordinateRadius_nonneg hmargin
  have htransitionBudget_nonneg :
      0 <= uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
        countDelta visitFloor rewardBound
          (uniformFloorStochasticRewardCoordinateRadius mdp episodes
            varianceProxy countDelta rewardDelta visitFloor) :=
    uniformFloorStochasticSelfConsistentTransitionBudget_nonneg
      hmargin hrewardBound_nonneg hrewardBudget_nonneg hq
  apply policy.iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret
    source initialState episodes hepisodes varianceProxy law htotal countDelta
      hcountDelta hcountDelta_le_one rewardDelta hrewardDelta
      hrewardDelta_le_one defaultState rewardBound
      (uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor)
      (uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
        countDelta visitFloor rewardBound
          (uniformFloorStochasticRewardCoordinateRadius mdp episodes
            varianceProxy countDelta rewardDelta visitFloor))
      hrewardBound hrewardBudget_nonneg htransitionBudget_nonneg
  · intro coordinate
    exact hmargin.trans_le (hcountFloor coordinate)
  · intro coordinate
    exact source.expectedCountRewardCoordinateRadius_le_uniformFloor policy
      initialState episodes varianceProxy countDelta rewardDelta visitFloor
      hmargin hcountFloor coordinate
  · exact policy.stochasticTransitionCover_of_uniformExpectedCountFloor_selfConsistent
      initialState episodes varianceProxy countDelta rewardDelta visitFloor
      rewardBound hmargin hcountFloor hrewardBound_nonneg hq

end MarkovPolicy

namespace DeterministicMarkovPolicyTable

/-- Exploratory path support feeds the shrinking fixed-policy calibration. -/
theorem exploratoryPolicy_iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_pathSupport_selfConsistentCalibration
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (source : mdp.MeanCompatibleRewardKernel)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (episodes : Nat) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1)
    (defaultState : State) (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      (episodes : Real) * visitFloor)
    (hq : uniformFloorStochasticTransitionContraction mdp episodes countDelta
      visitFloor < 1) :
    let policy := table.exploratoryPolicy explorationRate hexplorationRate
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticSelfConsistentTransitionBudget mdp episodes
        countDelta visitFloor rewardBound rewardBudget
    let event := source.stochasticAllCoordinateEmpiricalModelBadEvent policy
      initialState episodes varianceProxy countDelta rewardDelta
    MeasurableSet event /\
      (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
          event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta /\
      forall trajectories, trajectories ∉ event ->
        let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
          episodes (mdp.sampledEpisodeBatchOfStochasticTrajectories
            episodes trajectories) defaultState rewardBudget transitionBudget
        (forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              model.plan.upperValueRemaining mdp.horizon le_rfl state) /\
          model.plan.optimisticPolicy.expectedRegret initialState <=
            model.plan.optimisticPolicy.occupancySumRemaining
              (fun remaining hremaining state =>
                2 * model.plan.selectedRadiusRemaining
                  remaining hremaining state)
              mdp.horizon le_rfl initialState := by
  dsimp only
  apply MarkovPolicy.iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_uniformExpectedCountFloor_selfConsistent
    source (table.exploratoryPolicy explorationRate hexplorationRate)
      initialState episodes hepisodes varianceProxy law htotal countDelta
      hcountDelta hcountDelta_le_one rewardDelta hrewardDelta
      hrewardDelta_le_one defaultState rewardBound visitFloor hrewardBound
      hmargin
  · exact table.uniformVisitFloor_expectedCount_le initialState episodes support
      explorationRate hexplorationRate visitFloor hfloor
  · exact hq

end DeterministicMarkovPolicyTable

end BanditRLProof.FiniteHorizonRL
