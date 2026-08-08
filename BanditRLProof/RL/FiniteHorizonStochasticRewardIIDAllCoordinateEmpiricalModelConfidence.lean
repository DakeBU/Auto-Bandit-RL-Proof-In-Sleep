import BanditRLProof.RL.FiniteHorizonStochasticRewardIIDEmpiricalRewardConfidence

/-!
# All-coordinate iid empirical-model confidence with stochastic rewards

This module combines the compiled sampled-reward coordinate tail with the
existing simultaneous count/transition event.  It keeps the complete
reward-bearing iid trajectory family as the probability space and constructs
the empirical model from the actual sampled rewards.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MDP

/-- Reward erasure preserves the state immediately preceding every coordinate. -/
theorem rewardStepTrace_stateAt_eq_trajectoryStateAt_eraseTrajectory
    (mdp : MDP State Action)
    (trajectory : State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) :
    RewardStepTrace.stateAt trajectory.1 trajectory.2 stage =
      mdp.trajectoryStateAt
        (MeanCompatibleRewardKernel.eraseTrajectory
          (mdp := mdp) trajectory) stage := by
  unfold RewardStepTrace.stateAt trajectoryStateAt
    MeanCompatibleRewardKernel.eraseTrajectory RewardStepTrace.eraseRewards
  split_ifs <;> rfl

/-- Sampled and known-reward projections have identical stage states. -/
theorem sampledEpisodeStep_state_eq_knownRewardEpisodeStep
    (mdp : MDP State Action)
    (trajectory : State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) :
    (mdp.sampledEpisodeStepOfStochasticTrajectory trajectory stage).state =
      (mdp.episodeStepOfTrajectory
        (MeanCompatibleRewardKernel.eraseTrajectory
          (mdp := mdp) trajectory) stage).state := by
  exact mdp.rewardStepTrace_stateAt_eq_trajectoryStateAt_eraseTrajectory
    trajectory stage

/-- Sampled and known-reward projections have identical stage actions. -/
@[simp]
theorem sampledEpisodeStep_action_eq_knownRewardEpisodeStep
    (mdp : MDP State Action)
    (trajectory : State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) :
    (mdp.sampledEpisodeStepOfStochasticTrajectory trajectory stage).action =
      (mdp.episodeStepOfTrajectory
        (MeanCompatibleRewardKernel.eraseTrajectory
          (mdp := mdp) trajectory) stage).action := by
  rfl

/-- Sampled and known-reward projections have identical next states. -/
@[simp]
theorem sampledEpisodeStep_nextState_eq_knownRewardEpisodeStep
    (mdp : MDP State Action)
    (trajectory : State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) :
    (mdp.sampledEpisodeStepOfStochasticTrajectory trajectory stage).nextState =
      (mdp.episodeStepOfTrajectory
        (MeanCompatibleRewardKernel.eraseTrajectory
          (mdp := mdp) trajectory) stage).nextState := by
  rfl

/-- Actual sampled-reward and known-reward projections have the same visit counts. -/
theorem sampledEpisodeBatch_visitCount_eq_knownRewardEpisodeBatch
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes trajectories).visitCount
        stage state action =
      (MeanCompatibleRewardKernel.knownRewardEpisodeBatchOfStochasticTrajectories
        (mdp := mdp) episodes trajectories).visitCount stage state action := by
  classical
  unfold EpisodeBatch.visitCount
  apply Finset.sum_congr rfl
  intro episode _
  change
    (if
        (mdp.sampledEpisodeStepOfStochasticTrajectory
            (trajectories episode) stage).state = state /\
          (mdp.sampledEpisodeStepOfStochasticTrajectory
            (trajectories episode) stage).action = action then 1 else 0) =
      (if
        (mdp.episodeStepOfTrajectory
            (MeanCompatibleRewardKernel.eraseTrajectory
              (mdp := mdp) (trajectories episode)) stage).state = state /\
          (mdp.episodeStepOfTrajectory
            (MeanCompatibleRewardKernel.eraseTrajectory
              (mdp := mdp) (trajectories episode)) stage).action = action
        then 1 else 0)
  rw [mdp.sampledEpisodeStep_state_eq_knownRewardEpisodeStep
    (trajectories episode) stage]
  rfl

/-- Actual sampled-reward and known-reward projections have the same transition counts. -/
theorem sampledEpisodeBatch_transitionCount_eq_knownRewardEpisodeBatch
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes trajectories).transitionCount
        stage state action nextState =
      (MeanCompatibleRewardKernel.knownRewardEpisodeBatchOfStochasticTrajectories
        (mdp := mdp) episodes trajectories).transitionCount
          stage state action nextState := by
  classical
  unfold EpisodeBatch.transitionCount
  apply Finset.sum_congr rfl
  intro episode _
  change
    (if
        (mdp.sampledEpisodeStepOfStochasticTrajectory
            (trajectories episode) stage).state = state /\
          (mdp.sampledEpisodeStepOfStochasticTrajectory
              (trajectories episode) stage).action = action /\
            (mdp.sampledEpisodeStepOfStochasticTrajectory
              (trajectories episode) stage).nextState = nextState
      then 1 else 0) =
      (if
        (mdp.episodeStepOfTrajectory
            (MeanCompatibleRewardKernel.eraseTrajectory
              (mdp := mdp) (trajectories episode)) stage).state = state /\
          (mdp.episodeStepOfTrajectory
              (MeanCompatibleRewardKernel.eraseTrajectory
                (mdp := mdp) (trajectories episode)) stage).action = action /\
            (mdp.episodeStepOfTrajectory
              (MeanCompatibleRewardKernel.eraseTrajectory
                (mdp := mdp) (trajectories episode)) stage).nextState = nextState
      then 1 else 0)
  rw [mdp.sampledEpisodeStep_state_eq_knownRewardEpisodeStep
    (trajectories episode) stage]
  rfl

end MDP

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/--
Count event pulled back along the actual sampled-reward batch projection. Its
set is source-independent, while the receiver aligns it with the source's iid
stochastic trajectory measure and reward event used by the combined route.
-/
noncomputable def stochasticSampledBatchCountBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta : Real) :
    Set (Fin episodes -> State × RewardStepTrace Action State mdp.horizon) :=
  mdp.sampledEpisodeBatchOfStochasticTrajectories episodes ⁻¹'
    policy.simultaneousCountBadEvent initialState episodes delta

/-- Membership in the sampled and known-reward pullbacks of the count event agrees. -/
theorem mem_stochasticSampledBatchCountBadEvent_iff_knownReward
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta : Real)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) :
    trajectories ∈ source.stochasticSampledBatchCountBadEvent
        policy initialState episodes delta ↔
      MeanCompatibleRewardKernel.knownRewardEpisodeBatchOfStochasticTrajectories
          (mdp := mdp) episodes trajectories ∈
        policy.simultaneousCountBadEvent initialState episodes delta := by
  classical
  simp only [stochasticSampledBatchCountBadEvent,
    MarkovPolicy.simultaneousCountBadEvent, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨coordinate, hcoordinate⟩
    refine ⟨coordinate, ?_⟩
    cases coordinate with
    | visit stage state action =>
        simpa [CountCoordinate.badEvent, CountCoordinate.deviation,
          MDP.sampledEpisodeBatch_visitCount_eq_knownRewardEpisodeBatch]
          using hcoordinate
    | transition stage state action nextState =>
        simpa [CountCoordinate.badEvent, CountCoordinate.deviation,
          MDP.sampledEpisodeBatch_transitionCount_eq_knownRewardEpisodeBatch]
          using hcoordinate
  · rintro ⟨coordinate, hcoordinate⟩
    refine ⟨coordinate, ?_⟩
    cases coordinate with
    | visit stage state action =>
        simpa [CountCoordinate.badEvent, CountCoordinate.deviation,
          MDP.sampledEpisodeBatch_visitCount_eq_knownRewardEpisodeBatch]
          using hcoordinate
    | transition stage state action nextState =>
        simpa [CountCoordinate.badEvent, CountCoordinate.deviation,
          MDP.sampledEpisodeBatch_transitionCount_eq_knownRewardEpisodeBatch]
          using hcoordinate

/-- The pulled-back sampled-batch count event is measurable. -/
theorem measurableSet_stochasticSampledBatchCountBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta : Real) :
    MeasurableSet (source.stochasticSampledBatchCountBadEvent
      policy initialState episodes delta) :=
  (policy.measurableSet_simultaneousCountBadEvent
    initialState episodes delta).preimage
      (mdp.measurable_sampledEpisodeBatchOfStochasticTrajectories episodes)

/-- The actual sampled-batch count event inherits the compiled count failure share. -/
theorem iidStochasticTrajectoryFamilyMeasure_stochasticSampledBatchCountBadEvent_le
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
        (source.stochasticSampledBatchCountBadEvent
          policy initialState episodes delta) <=
      ENNReal.ofReal delta := by
  let mu := source.iidStochasticTrajectoryFamilyMeasure
    policy initialState episodes
  let knownBatch :=
    MeanCompatibleRewardKernel.knownRewardEpisodeBatchOfStochasticTrajectories
      (mdp := mdp) episodes
  let event := policy.simultaneousCountBadEvent initialState episodes delta
  have hevent : source.stochasticSampledBatchCountBadEvent
      policy initialState episodes delta = knownBatch ⁻¹' event := by
    ext trajectories
    exact source.mem_stochasticSampledBatchCountBadEvent_iff_knownReward
      policy initialState episodes delta trajectories
  rw [hevent]
  calc
    mu (knownBatch ⁻¹' event) = (mu.map knownBatch) event := by
      rw [Measure.map_apply
        (MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchOfStochasticTrajectories
          (mdp := mdp) episodes)
        (policy.measurableSet_simultaneousCountBadEvent
          initialState episodes delta)]
    _ = (policy.iidEpisodeBatchMeasure initialState episodes) event := by
      rw [source.iidStochasticTrajectoryFamilyMeasure_map_knownRewardEpisodeBatch_eq_iidEpisodeBatchMeasure]
    _ <= ENNReal.ofReal delta :=
      policy.iidEpisodeBatch_simultaneousCountBadEvent_le
        initialState episodes hepisodes delta hdelta hdelta_le_one

/-- Equal reward confidence share for every stage/state/action coordinate. -/
noncomputable def simultaneousRewardDelta
    (mdp : MDP State Action) (delta : Real) : Real :=
  delta / (Fintype.card (VisitCoordinate mdp) : Real)

/-- Deterministic fixed-coordinate reward-sum confidence radius. -/
noncomputable def simultaneousRewardSumConfidenceRadius
    (mdp : MDP State Action) (episodes : Nat)
    (varianceProxy : NNReal) (delta : Real) : Real :=
  Concentration.subGaussianSumConfidenceRadius
    ((episodes : NNReal) * varianceProxy)
    (simultaneousRewardDelta mdp delta)

/-- One visit coordinate's sampled-reward deviation event. -/
noncomputable def rewardCoordinateBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (episodes : Nat) (varianceProxy : NNReal) (delta : Real)
    (coordinate : VisitCoordinate mdp) :
    Set (Fin episodes -> State × RewardStepTrace Action State mdp.horizon) :=
  {trajectories |
    simultaneousRewardSumConfidenceRadius mdp episodes varianceProxy delta <=
      |∑ episode : Fin episodes,
        source.maskedRewardDeviationAtEpisode coordinate.stage coordinate.state
          coordinate.action episode trajectories|}

/-- Union of every stage/state/action sampled-reward deviation event. -/
noncomputable def simultaneousRewardBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (episodes : Nat) (varianceProxy : NNReal) (delta : Real) :
    Set (Fin episodes -> State × RewardStepTrace Action State mdp.horizon) :=
  ⋃ coordinate : VisitCoordinate mdp,
    source.rewardCoordinateBadEvent episodes varianceProxy delta coordinate

/-- Every fixed reward-coordinate event is measurable. -/
theorem measurableSet_rewardCoordinateBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (episodes : Nat) (varianceProxy : NNReal) (delta : Real)
    (coordinate : VisitCoordinate mdp) :
    MeasurableSet
      (source.rewardCoordinateBadEvent episodes varianceProxy delta coordinate) := by
  have hsum : Measurable
      (fun trajectories => ∑ episode : Fin episodes,
        source.maskedRewardDeviationAtEpisode coordinate.stage coordinate.state
          coordinate.action episode trajectories) := by
    refine Finset.measurable_sum Finset.univ fun episode _ => ?_
    exact (MDP.measurable_maskedRewardDeviationAt_trajectory mdp
      coordinate.stage coordinate.state coordinate.action).comp
        (measurable_pi_apply episode)
  exact measurableSet_le measurable_const hsum.abs

/-- The all-coordinate reward union is measurable. -/
theorem measurableSet_simultaneousRewardBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (episodes : Nat) (varianceProxy : NNReal) (delta : Real) :
    MeasurableSet
      (source.simultaneousRewardBadEvent episodes varianceProxy delta) := by
  unfold simultaneousRewardBadEvent
  exact MeasurableSet.iUnion fun coordinate =>
    source.measurableSet_rewardCoordinateBadEvent
      episodes varianceProxy delta coordinate

/-- A nonempty reward-coordinate family receives a positive equal share. -/
theorem simultaneousRewardDelta_pos
    (mdp : MDP State Action) (hcoordinate : Nonempty (VisitCoordinate mdp))
    {delta : Real} (hdelta : 0 < delta) :
    0 < simultaneousRewardDelta mdp delta := by
  unfold simultaneousRewardDelta
  exact div_pos hdelta (by
    exact_mod_cast Fintype.card_pos_iff.mpr hcoordinate)

/-- A global reward share at most one gives each coordinate a share at most one. -/
theorem simultaneousRewardDelta_le_one
    (mdp : MDP State Action) (hcoordinate : Nonempty (VisitCoordinate mdp))
    {delta : Real} (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    simultaneousRewardDelta mdp delta <= 1 := by
  have hcardNat : 0 < Fintype.card (VisitCoordinate mdp) :=
    Fintype.card_pos_iff.mpr hcoordinate
  have hcardReal : (1 : Real) <= Fintype.card (VisitCoordinate mdp) := by
    exact_mod_cast hcardNat
  exact (div_le_self (le_of_lt hdelta) hcardReal).trans hdelta_le_one

/-- The finite all-coordinate sampled-reward union consumes only its reward share. -/
theorem iidStochasticTrajectoryFamilyMeasure_simultaneousRewardBadEvent_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
        (source.simultaneousRewardBadEvent episodes varianceProxy delta) <=
      ENNReal.ofReal delta := by
  classical
  by_cases hcoordinate : Nonempty (VisitCoordinate mdp)
  · letI : Nonempty (VisitCoordinate mdp) := hcoordinate
    have htail : forall coordinate : VisitCoordinate mdp,
        coordinate ∈ (Finset.univ : Finset (VisitCoordinate mdp)) ->
          (source.iidStochasticTrajectoryFamilyMeasure
              policy initialState episodes)
              (source.rewardCoordinateBadEvent
                episodes varianceProxy delta coordinate) <=
            ENNReal.ofReal
              (delta /
                ((Finset.univ : Finset (VisitCoordinate mdp)).card : Real)) := by
      intro coordinate _
      simpa [rewardCoordinateBadEvent,
        simultaneousRewardSumConfidenceRadius, simultaneousRewardDelta] using
        source.iidStochasticTrajectoryFamilyMeasure_maskedRewardDeviation_sum_abs_tail_le
          policy initialState episodes coordinate.stage coordinate.state
            coordinate.action varianceProxy law htotal
            (simultaneousRewardDelta mdp delta)
            (simultaneousRewardDelta_pos mdp hcoordinate hdelta)
            (simultaneousRewardDelta_le_one
              mdp hcoordinate hdelta hdelta_le_one)
    simpa [simultaneousRewardBadEvent] using
      (ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
        (source.iidStochasticTrajectoryFamilyMeasure
          policy initialState episodes)
        (Finset.univ : Finset (VisitCoordinate mdp))
        Finset.univ_nonempty delta
        (fun coordinate => source.rewardCoordinateBadEvent
          episodes varianceProxy delta coordinate)
        htail)
  · have hcard : Fintype.card (VisitCoordinate mdp) = 0 :=
      Nat.eq_zero_of_not_pos fun hpos =>
        hcoordinate (Fintype.card_pos_iff.mp hpos)
    letI : IsEmpty (VisitCoordinate mdp) := Fintype.card_eq_zero_iff.mp hcard
    simp [simultaneousRewardBadEvent]

/-- Outside the reward union, every masked reward sum is strictly inside its radius. -/
theorem maskedRewardDeviation_sum_abs_lt_of_not_mem_simultaneousRewardBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    {episodes : Nat} {varianceProxy : NNReal} {delta : Real}
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon)
    (htrajectories : trajectories ∉
      source.simultaneousRewardBadEvent episodes varianceProxy delta)
    (coordinate : VisitCoordinate mdp) :
    |∑ episode : Fin episodes,
        source.maskedRewardDeviationAtEpisode coordinate.stage coordinate.state
          coordinate.action episode trajectories| <
      simultaneousRewardSumConfidenceRadius mdp episodes varianceProxy delta := by
  apply lt_of_not_ge
  intro hbad
  apply htrajectories
  exact Set.mem_iUnion.mpr ⟨coordinate, hbad⟩

/-- The masked iid reward sum is exactly reward sum minus visit count times mean. -/
theorem maskedRewardDeviation_sum_eq_sampledBatch_rewardSum_sub
    (source : MeanCompatibleRewardKernel mdp)
    {episodes : Nat}
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (∑ episode : Fin episodes,
        source.maskedRewardDeviationAtEpisode stage state action
          episode trajectories) =
      (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes trajectories).rewardSum
          stage state action -
        ((mdp.sampledEpisodeBatchOfStochasticTrajectories episodes trajectories).visitCount
          stage state action : Real) * mdp.reward state action := by
  classical
  simp only [maskedRewardDeviationAtEpisode, MDP.maskedRewardDeviationAt,
    MDP.sampledEpisodeBatchOfStochasticTrajectories,
    MDP.sampledEpisodeStepOfStochasticTrajectory,
    EpisodeBatch.rewardSum, EpisodeBatch.visitCount]
  rw [Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro episode _
  by_cases hvisit :
      RewardStepTrace.stateAt (trajectories episode).1
          (trajectories episode).2 stage = state /\
        ((trajectories episode).2 stage).1 = action
  · simp [hvisit]
  · simp [hvisit]

/--
Deterministic reward-mean radius based on the genuine lower count margin. Its
formula is source-independent; the receiver keeps it adjacent to the
source-indexed reward event and empirical-reward consumer.
-/
noncomputable def expectedCountRewardCoordinateRadius
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) (coordinate : VisitCoordinate mdp) : Real :=
  simultaneousRewardSumConfidenceRadius mdp episodes varianceProxy rewardDelta /
    (coordinate.expectedCount policy initialState episodes -
      simultaneousCountConfidenceRadius mdp episodes countDelta)

/-- Outside both events, a sampled empirical reward obeys its deterministic radius. -/
theorem sampledBatch_empiricalReward_abs_sub_le_expectedCountRewardCoordinateRadius
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    {episodes : Nat} {varianceProxy : NNReal}
    {countDelta rewardDelta : Real}
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon)
    (hcount : trajectories ∉ source.stochasticSampledBatchCountBadEvent
      policy initialState episodes countDelta)
    (hreward : trajectories ∉
      source.simultaneousRewardBadEvent episodes varianceProxy rewardDelta)
    (coordinate : VisitCoordinate mdp)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes countDelta <
      coordinate.expectedCount policy initialState episodes) :
    let batch := mdp.sampledEpisodeBatchOfStochasticTrajectories
      episodes trajectories
    |batch.empiricalReward coordinate.stage coordinate.state coordinate.action -
        mdp.reward coordinate.state coordinate.action| <=
      source.expectedCountRewardCoordinateRadius policy initialState episodes
        varianceProxy countDelta rewardDelta coordinate := by
  let batch := mdp.sampledEpisodeBatchOfStochasticTrajectories
    episodes trajectories
  let radius := simultaneousRewardSumConfidenceRadius
    mdp episodes varianceProxy rewardDelta
  let countRadius := simultaneousCountConfidenceRadius mdp episodes countDelta
  let expected := coordinate.expectedCount policy initialState episodes
  let count : Real := coordinate.count batch
  change
    |batch.empiricalReward coordinate.stage coordinate.state coordinate.action -
        mdp.reward coordinate.state coordinate.action| <=
      source.expectedCountRewardCoordinateRadius policy initialState episodes
        varianceProxy countDelta rewardDelta coordinate
  have hcountEvent : batch ∉
      policy.simultaneousCountBadEvent initialState episodes countDelta := by
    simpa [stochasticSampledBatchCountBadEvent, batch] using hcount
  have hcountPosNat : 0 < coordinate.count batch :=
    policy.visitCoordinate_count_pos_of_not_mem_simultaneousCountBadEvent
      initialState batch hcountEvent coordinate hmargin
  have hcountPos : 0 < count := by
    have : (0 : Real) < (coordinate.count batch : Real) := by
      exact_mod_cast hcountPosNat
    simpa [count] using this
  have hdenominator : 0 < expected - countRadius := by
    dsimp [expected, countRadius]
    linarith
  have hlower : expected - countRadius < count := by
    simpa [expected, countRadius, count] using
      policy.expectedCount_sub_radius_lt_count_of_not_mem_simultaneousCountBadEvent
        initialState batch hcountEvent coordinate
  have hsum :=
    source.maskedRewardDeviation_sum_abs_lt_of_not_mem_simultaneousRewardBadEvent
      trajectories hreward coordinate
  rw [source.maskedRewardDeviation_sum_eq_sampledBatch_rewardSum_sub
    trajectories coordinate.stage coordinate.state coordinate.action] at hsum
  have hradius : 0 <= radius := by
    exact Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have herror :
      batch.empiricalReward coordinate.stage coordinate.state coordinate.action -
          mdp.reward coordinate.state coordinate.action =
        (batch.rewardSum coordinate.stage coordinate.state coordinate.action -
            count * mdp.reward coordinate.state coordinate.action) / count := by
    have hcountNe : count ≠ 0 := ne_of_gt hcountPos
    have hvisitNe :
        (batch.visitCount coordinate.stage coordinate.state coordinate.action : Real) ≠
          0 := by
      simpa [count, VisitCoordinate.count] using hcountNe
    dsimp [EpisodeBatch.empiricalReward, count, VisitCoordinate.count]
    field_simp [hvisitNe]
  rw [herror, abs_div, abs_of_pos hcountPos]
  calc
    |batch.rewardSum coordinate.stage coordinate.state coordinate.action -
        count * mdp.reward coordinate.state coordinate.action| / count <=
        radius / count := by
      apply div_le_div_of_nonneg_right (le_of_lt ?_) hcountPos.le
      simpa [batch, radius, count, VisitCoordinate.count] using hsum
    _ <= radius / (expected - countRadius) :=
      div_le_div_of_nonneg_left hradius hdenominator (le_of_lt hlower)
    _ = source.expectedCountRewardCoordinateRadius policy initialState episodes
        varianceProxy countDelta rewardDelta coordinate := by
      rfl

end MDP.MeanCompatibleRewardKernel

/-- Linear value envelope with one empirical-reward error and one reward bonus. -/
def stochasticEmpiricalFiniteBatchValueEnvelope
    (rewardBound rewardBudget transitionBudget : Real)
    (remaining : Nat) : Real :=
  (remaining : Real) *
    (rewardBound + 2 * rewardBudget + transitionBudget)

namespace MDP

/-- Canonical empirical model retaining sampled rewards and fixed reward/transition budgets. -/
noncomputable def stochasticAllCoordinateEmpiricalFiniteBatchModel
    (mdp : MDP State Action) (episodes : Nat)
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (rewardBudget transitionBudget : Real) :
    FiniteBatchModel mdp episodes where
  batch := batch
  defaultState := defaultState
  rewardRadius _stage _state _action := rewardBudget
  transitionRadius _stage _state _action := transitionBudget

namespace StochasticAllCoordinateConfidence

variable {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (rewardBound rewardBudget transitionBudget : Real)

/-- Reward error and fixed budgets give a noncircular linear optimistic-value envelope. -/
theorem upperValueRemaining_abs_le
    (hrewardError : forall stage state action,
      |batch.empiricalReward stage state action - mdp.reward state action| <=
        rewardBudget)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hrewardBudget_nonneg : 0 <= rewardBudget)
    (htransitionBudget_nonneg : 0 <= transitionBudget) :
    forall (remaining : Nat) (hremaining : remaining <= mdp.horizon)
        (state : State),
      |(mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes batch
          defaultState rewardBudget transitionBudget).plan.upperValueRemaining
          remaining hremaining state| <=
        stochasticEmpiricalFiniteBatchValueEnvelope
          rewardBound rewardBudget transitionBudget remaining := by
  let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
    episodes batch defaultState rewardBudget transitionBudget
  change forall (remaining : Nat) (hremaining : remaining <= mdp.horizon)
      (state : State),
    |model.plan.upperValueRemaining remaining hremaining state| <=
      stochasticEmpiricalFiniteBatchValueEnvelope
        rewardBound rewardBudget transitionBudget remaining
  intro remaining
  induction remaining with
  | zero =>
      intro hremaining state
      simp [MDP.EstimatedModelPlan.upperValueRemaining,
        stochasticEmpiricalFiniteBatchValueEnvelope]
  | succ remaining ih =>
      intro hremaining state
      let stage := mdp.decisionStageRemaining remaining hremaining
      let tail := model.plan.upperValueRemaining remaining (by omega)
      let action := model.plan.optimisticAction stage tail state
      have htail : forall nextState, |tail nextState| <=
          stochasticEmpiricalFiniteBatchValueEnvelope
            rewardBound rewardBudget transitionBudget remaining := by
        intro nextState
        exact ih (by omega) nextState
      have htransition :
          |model.plan.transitionValue stage tail state action| <=
            stochasticEmpiricalFiniteBatchValueEnvelope
              rewardBound rewardBudget transitionBudget remaining := by
        rw [← Real.norm_eq_abs]
        have hnorm := norm_integral_le_of_norm_le_const
          (μ := model.plan.estimatedTransition stage (state, action))
          (C := stochasticEmpiricalFiniteBatchValueEnvelope
            rewardBound rewardBudget transitionBudget remaining)
          (Filter.Eventually.of_forall fun nextState => by
            rw [Real.norm_eq_abs]
            exact htail nextState)
        simpa [MDP.EstimatedModelPlan.transitionValue] using hnorm
      have hempiricalReward :
          |batch.empiricalReward stage state action| <=
            rewardBound + rewardBudget := by
        calc
          |batch.empiricalReward stage state action| =
              |(batch.empiricalReward stage state action -
                  mdp.reward state action) + mdp.reward state action| := by
                congr 1
                ring
          _ <= |batch.empiricalReward stage state action -
                mdp.reward state action| + |mdp.reward state action| :=
            abs_add_le _ _
          _ <= rewardBound + rewardBudget := by
            linarith [hrewardError stage state action,
              hrewardBound state action]
      rw [MDP.EstimatedModelPlan.upperValueRemaining]
      change
        |batch.empiricalReward stage state action +
              model.plan.transitionValue stage tail state action +
            rewardBudget + transitionBudget| <=
          stochasticEmpiricalFiniteBatchValueEnvelope
            rewardBound rewardBudget transitionBudget (remaining + 1)
      calc
        |batch.empiricalReward stage state action +
              model.plan.transitionValue stage tail state action +
            rewardBudget + transitionBudget| <=
            |batch.empiricalReward stage state action| +
              |model.plan.transitionValue stage tail state action| +
              |rewardBudget| + |transitionBudget| := by
          calc
            _ <= |batch.empiricalReward stage state action +
                    model.plan.transitionValue stage tail state action +
                  rewardBudget| + |transitionBudget| := abs_add_le _ _
            _ <= (|batch.empiricalReward stage state action +
                    model.plan.transitionValue stage tail state action| +
                  |rewardBudget|) + |transitionBudget| := by
                gcongr
                exact abs_add_le _ _
            _ <= ((|batch.empiricalReward stage state action| +
                    |model.plan.transitionValue stage tail state action|) +
                  |rewardBudget|) + |transitionBudget| := by
                gcongr
                exact abs_add_le _ _
            _ = _ := by ring
        _ <= (rewardBound + rewardBudget) +
              stochasticEmpiricalFiniteBatchValueEnvelope
                rewardBound rewardBudget transitionBudget remaining +
              rewardBudget + transitionBudget := by
          rw [abs_of_nonneg hrewardBudget_nonneg,
            abs_of_nonneg htransitionBudget_nonneg]
          linarith
        _ = stochasticEmpiricalFiniteBatchValueEnvelope
              rewardBound rewardBudget transitionBudget (remaining + 1) := by
          unfold stochasticEmpiricalFiniteBatchValueEnvelope
          rw [show ((remaining + 1 : Nat) : Real) =
            (remaining : Real) + 1 by norm_num]
          ring

end StochasticAllCoordinateConfidence
end MDP

namespace MarkovPolicy

/-- Pathwise stochastic sampled-batch producer for the complete confidence object. -/
noncomputable def stochasticAllCoordinateEmpiricalFiniteBatchModelConfidence_of_not_mem
    {mdp : MDP State Action}
    (source : mdp.MeanCompatibleRewardKernel)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    {episodes : Nat} {varianceProxy : NNReal}
    {countDelta rewardDelta : Real}
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon)
    (hcount : trajectories ∉ source.stochasticSampledBatchCountBadEvent
      policy initialState episodes countDelta)
    (hreward : trajectories ∉
      source.simultaneousRewardBadEvent episodes varianceProxy rewardDelta)
    (defaultState : State)
    (rewardBound rewardBudget transitionBudget : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hrewardBudget_nonneg : 0 <= rewardBudget)
    (htransitionBudget_nonneg : 0 <= transitionBudget)
    (hmargin : forall coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes countDelta <
        coordinate.expectedCount policy initialState episodes)
    (hrewardCover : forall coordinate : VisitCoordinate mdp,
      source.expectedCountRewardCoordinateRadius policy initialState episodes
          varianceProxy countDelta rewardDelta coordinate <= rewardBudget)
    (htransitionCover : forall (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes countDelta
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            stochasticEmpiricalFiniteBatchValueEnvelope
              rewardBound rewardBudget transitionBudget remaining) <=
        transitionBudget) :
    (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes
      (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes trajectories)
      defaultState rewardBudget transitionBudget).Confidence := by
  let batch := mdp.sampledEpisodeBatchOfStochasticTrajectories
    episodes trajectories
  change (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes batch
    defaultState rewardBudget transitionBudget).Confidence
  have hcountEvent : batch ∉
      policy.simultaneousCountBadEvent initialState episodes countDelta := by
    simpa [MDP.MeanCompatibleRewardKernel.stochasticSampledBatchCountBadEvent,
      batch] using hcount
  have hrewardError : forall stage state action,
      |batch.empiricalReward stage state action - mdp.reward state action| <=
        rewardBudget := by
    intro stage state action
    let coordinate : VisitCoordinate mdp :=
      { stage := stage, state := state, action := action }
    have hcoordinate :=
      source.sampledBatch_empiricalReward_abs_sub_le_expectedCountRewardCoordinateRadius
        policy initialState trajectories hcount hreward coordinate
          (hmargin coordinate)
    have hcoordinate' :
        |batch.empiricalReward stage state action - mdp.reward state action| <=
          source.expectedCountRewardCoordinateRadius policy initialState episodes
            varianceProxy countDelta rewardDelta coordinate := by
      simpa [batch, coordinate] using hcoordinate
    exact hcoordinate'.trans (hrewardCover coordinate)
  exact
    { transitionCoordinateRadius :=
        policy.expectedCountTransitionCoordinateRadius
          initialState episodes countDelta
      valueEnvelope :=
        stochasticEmpiricalFiniteBatchValueEnvelope
          rewardBound rewardBudget transitionBudget
      rewardError_le_radius := by
        intro stage state action
        simpa [MDP.stochasticAllCoordinateEmpiricalFiniteBatchModel] using
          hrewardError stage state action
      transitionFrequencyError_le_radius := by
        intro remaining hremaining state action nextState
        let coordinate : VisitCoordinate mdp :=
          { stage := mdp.decisionStageRemaining remaining hremaining
            state := state
            action := action }
        simpa [coordinate] using
          policy.empiricalTransitionMass_abs_sub_transition_le_expectedCountRadius_of_not_mem
            initialState batch hcountEvent defaultState coordinate
              (hmargin coordinate) nextState
      upperValue_abs_le_envelope := by
        intro remaining hremaining state
        exact MDP.StochasticAllCoordinateConfidence.upperValueRemaining_abs_le
          (mdp := mdp) (batch := batch) (defaultState := defaultState)
          (rewardBound := rewardBound) (rewardBudget := rewardBudget)
          (transitionBudget := transitionBudget)
          hrewardError hrewardBound hrewardBudget_nonneg
          htransitionBudget_nonneg remaining (by omega) state
      transitionRadius_cover := by
        intro remaining hremaining state action
        simpa [MDP.stochasticAllCoordinateEmpiricalFiniteBatchModel] using
          htransitionCover remaining hremaining state action }

end MarkovPolicy

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/--
The one bad event used by the stochastic empirical-model route: the pulled-back
count event or one of the sampled-reward coordinate events.
-/
noncomputable def stochasticAllCoordinateEmpiricalModelBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) :
    Set (Fin episodes -> State × RewardStepTrace Action State mdp.horizon) :=
  source.stochasticSampledBatchCountBadEvent
      policy initialState episodes countDelta ∪
    source.simultaneousRewardBadEvent episodes varianceProxy rewardDelta

/-- The combined count-and-reward empirical-model event is measurable. -/
theorem measurableSet_stochasticAllCoordinateEmpiricalModelBadEvent
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) :
    MeasurableSet (source.stochasticAllCoordinateEmpiricalModelBadEvent
      policy initialState episodes varianceProxy countDelta rewardDelta) := by
  exact
    (source.measurableSet_stochasticSampledBatchCountBadEvent
      policy initialState episodes countDelta).union
      (source.measurableSet_simultaneousRewardBadEvent
        episodes varianceProxy rewardDelta)

/-- The two separately calibrated failure shares add under the combined event. -/
theorem iidStochasticTrajectoryFamilyMeasure_stochasticAllCoordinateEmpiricalModelBadEvent_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1) :
    (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
        (source.stochasticAllCoordinateEmpiricalModelBadEvent
          policy initialState episodes varianceProxy countDelta rewardDelta) <=
      ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta := by
  unfold stochasticAllCoordinateEmpiricalModelBadEvent
  exact (measure_union_le _ _).trans (add_le_add
    (source.iidStochasticTrajectoryFamilyMeasure_stochasticSampledBatchCountBadEvent_le
      policy initialState episodes hepisodes countDelta hcountDelta
        hcountDelta_le_one)
    (source.iidStochasticTrajectoryFamilyMeasure_simultaneousRewardBadEvent_le
      policy initialState episodes varianceProxy law htotal rewardDelta
        hrewardDelta hrewardDelta_le_one))

end MDP.MeanCompatibleRewardKernel

namespace MarkovPolicy

/--
The iid stochastic-reward trajectory law produces a measurable all-coordinate
confidence event for the empirical model built from the actual sampled rewards.
-/
theorem iidStochasticTrajectoryFamilyMeasure_allCoordinate_finiteBatchModel_confidence
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
    (defaultState : State)
    (rewardBound rewardBudget transitionBudget : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hrewardBudget_nonneg : 0 <= rewardBudget)
    (htransitionBudget_nonneg : 0 <= transitionBudget)
    (hmargin : forall coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes countDelta <
        coordinate.expectedCount policy initialState episodes)
    (hrewardCover : forall coordinate : VisitCoordinate mdp,
      source.expectedCountRewardCoordinateRadius policy initialState episodes
          varianceProxy countDelta rewardDelta coordinate <= rewardBudget)
    (htransitionCover : forall (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes countDelta
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            stochasticEmpiricalFiniteBatchValueEnvelope
              rewardBound rewardBudget transitionBudget remaining) <=
        transitionBudget) :
    let event := source.stochasticAllCoordinateEmpiricalModelBadEvent
      policy initialState episodes varianceProxy countDelta rewardDelta
    MeasurableSet event ∧
      (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
          event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta ∧
      forall trajectories, trajectories ∉ event ->
        Nonempty
          (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes
            (mdp.sampledEpisodeBatchOfStochasticTrajectories
              episodes trajectories)
            defaultState rewardBudget transitionBudget).Confidence := by
  dsimp only
  refine ⟨source.measurableSet_stochasticAllCoordinateEmpiricalModelBadEvent
      policy initialState episodes varianceProxy countDelta rewardDelta,
    source.iidStochasticTrajectoryFamilyMeasure_stochasticAllCoordinateEmpiricalModelBadEvent_le
      policy initialState episodes hepisodes varianceProxy law htotal
        countDelta hcountDelta hcountDelta_le_one rewardDelta hrewardDelta
        hrewardDelta_le_one, ?_⟩
  intro trajectories htrajectories
  have hcount : trajectories ∉ source.stochasticSampledBatchCountBadEvent
      policy initialState episodes countDelta := by
    intro hbad
    exact htrajectories (Or.inl hbad)
  have hreward : trajectories ∉
      source.simultaneousRewardBadEvent episodes varianceProxy rewardDelta := by
    intro hbad
    exact htrajectories (Or.inr hbad)
  exact ⟨policy.stochasticAllCoordinateEmpiricalFiniteBatchModelConfidence_of_not_mem
    source initialState trajectories hcount hreward defaultState rewardBound
      rewardBudget transitionBudget hrewardBound hrewardBudget_nonneg
      htransitionBudget_nonneg hmargin hrewardCover htransitionCover⟩

/--
Outside the compiled stochastic empirical-model event, the sampled model is
globally optimistic and its recommended policy satisfies the existing
selected-radius expected-regret bound.
-/
theorem iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret
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
    (defaultState : State)
    (rewardBound rewardBudget transitionBudget : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hrewardBudget_nonneg : 0 <= rewardBudget)
    (htransitionBudget_nonneg : 0 <= transitionBudget)
    (hmargin : forall coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes countDelta <
        coordinate.expectedCount policy initialState episodes)
    (hrewardCover : forall coordinate : VisitCoordinate mdp,
      source.expectedCountRewardCoordinateRadius policy initialState episodes
          varianceProxy countDelta rewardDelta coordinate <= rewardBudget)
    (htransitionCover : forall (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes countDelta
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            stochasticEmpiricalFiniteBatchValueEnvelope
              rewardBound rewardBudget transitionBudget remaining) <=
        transitionBudget) :
    let event := source.stochasticAllCoordinateEmpiricalModelBadEvent
      policy initialState episodes varianceProxy countDelta rewardDelta
    MeasurableSet event ∧
      (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
          event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta ∧
      forall trajectories, trajectories ∉ event ->
        let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes
          (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes trajectories)
          defaultState rewardBudget transitionBudget
        (forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              model.plan.upperValueRemaining mdp.horizon le_rfl state) ∧
          model.plan.optimisticPolicy.expectedRegret initialState <=
            model.plan.optimisticPolicy.occupancySumRemaining
              (fun remaining hremaining state =>
                2 * model.plan.selectedRadiusRemaining
                  remaining hremaining state)
              mdp.horizon le_rfl initialState := by
  obtain ⟨hmeasurable, htail, hconfidence⟩ :=
    policy.iidStochasticTrajectoryFamilyMeasure_allCoordinate_finiteBatchModel_confidence
      source initialState episodes hepisodes varianceProxy law htotal
        countDelta hcountDelta hcountDelta_le_one rewardDelta hrewardDelta
        hrewardDelta_le_one defaultState rewardBound rewardBudget transitionBudget
        hrewardBound hrewardBudget_nonneg htransitionBudget_nonneg hmargin
        hrewardCover htransitionCover
  refine ⟨hmeasurable, htail, ?_⟩
  intro trajectories htrajectories
  obtain ⟨confidence⟩ := hconfidence trajectories htrajectories
  exact confidence
    |>.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
      initialState

end MarkovPolicy

end FiniteHorizonRL
end BanditRLProof
