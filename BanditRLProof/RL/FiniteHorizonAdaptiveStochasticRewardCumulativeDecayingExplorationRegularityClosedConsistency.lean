import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationConsistency
import BanditRLProof.RL.FiniteHorizonEpisodeBatchStandardBorel

/-!
# Regularity-closed stochastic decaying-exploration consistency

This module discharges the composite Standard Borel premises exposed by the
finite-window and all-window realized-behavior consistency endpoints.  The
state and action spaces remain the only caller-facing Standard Borel contract;
the finite batch and countable trajectory instances are inferred locally.

The probability, support, bounded-mean, sub-Gaussian, horizon, and positive
visit-floor assumptions are unchanged.  In particular, this remains a family
of changing finite-window laws, not a common-process almost-sure or anytime
statement.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveCumulativeStochasticEmpiricalOptimisticSource

/--
One scheduled stochastic window with every composite Standard Borel instance
inferred from the state and action spaces.
-/
theorem exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency_of_standardBorel
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real) (n : Nat)
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
    let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
    let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
    let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n
    let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
      mdp baseVisitFloor n
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp rounds delta visitFloor
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
    let projection :=
      MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
        (mdp := mdp) episodes
    let countBadEvent := projectedAdaptiveCumulativeCountBadEvent
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        rounds delta
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds 1 rewardVarianceProxy delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    let violationSet :=
      decayingExplorationAverageRealizedBehaviorRegretViolationSet mdp
        initialState rewardSource initialTable defaultState baseVisitFloor
          rewardVarianceProxy n
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n /\
      violationSet ⊆ combinedBadEvent /\
      source.trajectoryMeasure violationSet <=
        AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              (projection trajectory) defaultState countRadius round
              ).upperValueRemaining mdp.horizon le_rfl state) /\
        source.realizedSuccessorAverageRegret trajectory rounds <=
          AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor rewardVarianceProxy n := by
  exact
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency
      mdp initialState baseVisitFloor n rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor

/--
All scheduled stochastic windows and the joint scalar limit, with no indexed
batch or trajectory Standard Borel witnesses supplied by the caller.
-/
theorem exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_decayingExplorationAverageRealizedBehaviorConsistency_allWindows_of_standardBorel
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
        (fun n =>
          (AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n,
            AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
              mdp baseVisitFloor rewardVarianceProxy n))
        atTop (nhds (0, 0)) /\
      forall n,
        let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
        let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
        let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
        let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
          mdp baseVisitFloor n
        let episodes :=
          AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
            mdp baseVisitFloor n
        let countRadius :=
          AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
            mdp rounds delta visitFloor
        let source := exploratorySource mdp initialState episodes rewardSource
          initialTable defaultState countRadius explorationRate
            (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        let projection :=
          MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
            (mdp := mdp) episodes
        let countBadEvent := projectedAdaptiveCumulativeCountBadEvent
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          initialTable defaultState countRadius explorationRate
            (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
            rounds delta
        let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
          rounds 1 rewardVarianceProxy delta
        let combinedBadEvent := countBadEvent ∪ returnBadEvent
        let violationSet :=
          decayingExplorationAverageRealizedBehaviorRegretViolationSet mdp
            initialState rewardSource initialTable defaultState baseVisitFloor
              rewardVarianceProxy n
        MeasurableSet combinedBadEvent /\
          source.trajectoryMeasure combinedBadEvent <=
            AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n /\
          violationSet ⊆ combinedBadEvent /\
          source.trajectoryMeasure violationSet <=
            AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n /\
          forall trajectory, trajectory ∉ combinedBadEvent ->
            (forall round : Fin rounds, forall state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state <=
                (adaptiveCumulativeEmpiricalOptimisticPlanAt
                  (projection trajectory) defaultState countRadius round
                  ).upperValueRemaining mdp.horizon le_rfl state) /\
            source.realizedSuccessorAverageRegret trajectory rounds <=
              AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
                mdp baseVisitFloor rewardVarianceProxy n := by
  constructor
  · exact
      AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureAndRegretBound_tendsto_zero
        mdp hhorizon baseVisitFloor hbaseVisitFloor rewardVarianceProxy
  · intro n
    exact
      exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency_of_standardBorel
        mdp initialState baseVisitFloor n rewardSource rewardVarianceProxy law
          initialTable defaultState support hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor

end AdaptiveCumulativeStochasticEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
