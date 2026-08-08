import BanditRLProof.RL.FiniteHorizonStochasticRewardIIDAllCoordinateEmpiricalModelConfidence
import BanditRLProof.RL.FiniteHorizonExploratoryPathSupportExplicitCalibration

/-!
# Explicit stochastic-reward iid empirical-model calibration

This module replaces the coordinatewise margin and cover inputs of the
stochastic-reward iid empirical-model terminal by one common expected-count
floor and one scalar half-contraction condition. The reward and transition
budgets are explicit functions of that floor.
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

/-- Uniform reward-mean radius obtained from one common expected-count floor. -/
noncomputable def uniformFloorStochasticRewardCoordinateRadius
    (mdp : MDP State Action) (episodes : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta visitFloor : Real) : Real :=
  MDP.MeanCompatibleRewardKernel.simultaneousRewardSumConfidenceRadius
      mdp episodes varianceProxy rewardDelta /
    ((episodes : Real) * visitFloor -
      simultaneousCountConfidenceRadius mdp episodes countDelta)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The uniform reward radius is nonnegative under the strict count margin. -/
theorem uniformFloorStochasticRewardCoordinateRadius_nonneg
    {mdp : MDP State Action} {episodes : Nat} {varianceProxy : NNReal}
    {countDelta rewardDelta visitFloor : Real}
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      (episodes : Real) * visitFloor) :
    0 <= uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
  countDelta rewardDelta visitFloor := by
  unfold uniformFloorStochasticRewardCoordinateRadius
  exact div_nonneg
    (Concentration.subGaussianSumConfidenceRadius_nonneg _ _)
    (sub_nonneg.mpr hmargin.le)

/-- The explicit transition budget paired with the uniform reward budget. -/
def uniformFloorStochasticTransitionBudget
    (rewardBound rewardBudget : Real) : Real :=
  rewardBound + 2 * rewardBudget

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A common expected-count floor dominates every coordinate reward radius. -/
theorem expectedCountRewardCoordinateRadius_le_uniformFloor
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta visitFloor : Real)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      (episodes : Real) * visitFloor)
    (hcountFloor : forall coordinate : VisitCoordinate mdp,
      (episodes : Real) * visitFloor <=
        coordinate.expectedCount policy initialState episodes)
    (coordinate : VisitCoordinate mdp) :
    source.expectedCountRewardCoordinateRadius policy initialState episodes
        varianceProxy countDelta rewardDelta coordinate <=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor := by
  have hradius :
      0 <= simultaneousRewardSumConfidenceRadius mdp episodes varianceProxy
        rewardDelta :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hdenominator :
      0 < (episodes : Real) * visitFloor -
        simultaneousCountConfidenceRadius mdp episodes countDelta := by
    linarith
  have hdenominator_le :
      (episodes : Real) * visitFloor -
          simultaneousCountConfidenceRadius mdp episodes countDelta <=
        coordinate.expectedCount policy initialState episodes -
          simultaneousCountConfidenceRadius mdp episodes countDelta := by
    linarith [hcountFloor coordinate]
  unfold expectedCountRewardCoordinateRadius
  unfold uniformFloorStochasticRewardCoordinateRadius
  exact div_le_div_of_nonneg_left hradius hdenominator hdenominator_le

end MDP.MeanCompatibleRewardKernel

namespace MarkovPolicy

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/--
The common count floor and half-contraction condition cover every stochastic
transition-radius/value-envelope sum with the explicit transition budget.
-/
theorem stochasticTransitionCover_of_uniformExpectedCountFloor
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
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes countDelta
            visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticTransitionBudget rewardBound rewardBudget
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
    uniformFloorStochasticTransitionBudget rewardBound rewardBudget
  have hrewardBudget_nonneg : 0 <= rewardBudget := by
    exact uniformFloorStochasticRewardCoordinateRadius_nonneg hmargin
  have htransitionBudget_nonneg : 0 <= transitionBudget := by
    dsimp [transitionBudget, uniformFloorStochasticTransitionBudget]
    positivity
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
          (remaining : Real)) * (2 * transitionBudget) := by
      simp [stochasticEmpiricalFiniteBatchValueEnvelope,
        transitionBudget, uniformFloorStochasticTransitionBudget]
      ring
    _ <= ((Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes countDelta
            visitFloor *
          (mdp.horizon : Real)) * (2 * transitionBudget) := by
      gcongr
    _ <= (1 / 2 : Real) * (2 * transitionBudget) := by
      exact mul_le_mul_of_nonneg_right hcontraction
        (mul_nonneg (by norm_num) htransitionBudget_nonneg)
    _ = transitionBudget := by ring

/--
Fixed-policy route endpoint with every coordinate margin and cover produced by
one common expected-count floor and one scalar half-contraction condition.
-/
theorem iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_uniformExpectedCountFloor
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
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes countDelta
            visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticTransitionBudget rewardBound rewardBudget
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
      0 <= uniformFloorStochasticTransitionBudget rewardBound
        (uniformFloorStochasticRewardCoordinateRadius mdp episodes
          varianceProxy countDelta rewardDelta visitFloor) := by
    unfold uniformFloorStochasticTransitionBudget
    positivity
  apply policy.iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret
    source initialState episodes hepisodes varianceProxy law htotal
      countDelta hcountDelta hcountDelta_le_one rewardDelta hrewardDelta
      hrewardDelta_le_one defaultState rewardBound
      (uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor)
      (uniformFloorStochasticTransitionBudget rewardBound
        (uniformFloorStochasticRewardCoordinateRadius mdp episodes
          varianceProxy countDelta rewardDelta visitFloor))
      hrewardBound hrewardBudget_nonneg htransitionBudget_nonneg
  · intro coordinate
    exact hmargin.trans_le (hcountFloor coordinate)
  · intro coordinate
    exact source.expectedCountRewardCoordinateRadius_le_uniformFloor policy
      initialState episodes varianceProxy countDelta rewardDelta visitFloor
      hmargin hcountFloor coordinate
  · exact policy.stochasticTransitionCover_of_uniformExpectedCountFloor
      initialState episodes varianceProxy countDelta rewardDelta visitFloor
      rewardBound hmargin hcountFloor hrewardBound_nonneg hcontraction

end MarkovPolicy

namespace DeterministicMarkovPolicyTable

/--
Practical endpoint: exploratory path support constructs the common count floor,
then the explicit stochastic calibration yields confidence and recommended
expected regret for the exploratory policy's sampled-reward empirical model.
-/
theorem exploratoryPolicy_iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_pathSupport_explicitCalibration
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
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes countDelta
            visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
    let policy := table.exploratoryPolicy explorationRate hexplorationRate
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        countDelta rewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticTransitionBudget rewardBound rewardBudget
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
  apply MarkovPolicy.iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_uniformExpectedCountFloor
    source (table.exploratoryPolicy explorationRate hexplorationRate)
      initialState episodes hepisodes varianceProxy law htotal countDelta
      hcountDelta hcountDelta_le_one rewardDelta hrewardDelta
      hrewardDelta_le_one defaultState rewardBound visitFloor hrewardBound
      hmargin
  · exact table.uniformVisitFloor_expectedCount_le initialState episodes support
      explorationRate hexplorationRate visitFloor hfloor
  · exact hcontraction

end DeterministicMarkovPolicyTable

end BanditRLProof.FiniteHorizonRL
