import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentRealizedBehaviorRegret
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationConsistency
import BanditRLProof.RL.FiniteHorizonExploratoryPathSupportEpisodeThreshold
import BanditRLProof.RL.FiniteHorizonEpisodeBatchStandardBorel

/-!
# Scheduled self-consistent realized regret for actual sampled optimism

This module gives the self-consistent actual-sampled route an explicit
horizon-indexed batch schedule.  It reuses the decaying exploration, round,
visit-floor, and confidence schedules, and chooses one `ceil + 1` episode count
above three explicit thresholds: the existing count-calibration threshold, a
shrinking count-ratio threshold, and a shrinking sampled-reward threshold.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/-- Explicit episode threshold making the normalized count radius smaller than `scale⁻²`. -/
noncomputable def selfConsistentCountShrinkEpisodeThreshold
    (mdp : MDP State Action) (rounds : Nat) (delta visitFloor scale : Real) : Real :=
  scale ^ 4 *
      Real.log
        (2 / simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta)) /
    (2 * visitFloor ^ 2)

/-- Explicit episode threshold making the uniform sampled-reward radius smaller than `scale⁻²`. -/
noncomputable def selfConsistentRewardShrinkEpisodeThreshold
    (mdp : MDP State Action) (rounds : Nat) (varianceProxy : NNReal)
    (delta visitFloor scale : Real) : Real :=
  8 * (varianceProxy : Real) *
      Real.log
        (2 / MDP.MeanCompatibleRewardKernel.simultaneousRewardDelta mdp
          (multiBatchLocalDelta rounds delta)) *
      scale ^ 4 /
    visitFloor ^ 2

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- The count threshold gives a scale-squared normalized count-radius bound. -/
theorem simultaneousCountConfidenceRadius_lt_episodes_mul_visitFloor_div_scale_sq_of_threshold
    (mdp : MDP State Action) {rounds episodes : Nat}
    {delta visitFloor scale : Real}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor)
    (hscale : 0 < scale)
    (hthreshold : selfConsistentCountShrinkEpisodeThreshold mdp rounds delta
        visitFloor scale < (episodes : Real)) :
    simultaneousCountConfidenceRadius mdp episodes
        (multiBatchLocalDelta rounds delta) <
      (episodes : Real) * visitFloor / scale ^ 2 := by
  let witnessState : State := Classical.choice inferInstance
  let witnessAction : Action := Classical.choice inferInstance
  have hcoordinate : Nonempty (CountCoordinate mdp) :=
    ⟨CountCoordinate.visit ⟨0, hhorizon⟩ witnessState witnessAction⟩
  have hroundsReal : (0 : Real) < rounds := by exact_mod_cast hrounds
  have hlocalPos : 0 < multiBatchLocalDelta rounds delta :=
    div_pos hdelta hroundsReal
  have hlocalLeOne : multiBatchLocalDelta rounds delta <= 1 :=
    (div_le_self hdelta.le (by exact_mod_cast hrounds)).trans hdelta_le_one
  have hcoordinatePos :
      0 < simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta) :=
    MarkovPolicy.simultaneousCountDelta_pos hcoordinate hlocalPos
  have hcoordinateLeOne :
      simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta) <= 1 :=
    MarkovPolicy.simultaneousCountDelta_le_one hcoordinate hlocalPos hlocalLeOne
  let radius := simultaneousCountConfidenceRadius mdp episodes
    (multiBatchLocalDelta rounds delta)
  let logarithm := Real.log
    (2 / simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta))
  have hepisodesReal : (0 : Real) < episodes := by exact_mod_cast hepisodes
  have hradiusNonneg : 0 <= radius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hradiusSq : radius ^ 2 = (episodes : Real) / 2 * logarithm := by
    change
      (Concentration.subGaussianSumConfidenceRadius
          (MarkovPolicy.iidBernoulliVarianceProxy episodes)
          (simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta))) ^ 2 =
        (episodes : Real) / 2 * logarithm
    rw [Concentration.subGaussianSumConfidenceRadius_sq _ _
      hcoordinatePos hcoordinateLeOne]
    rw [MarkovPolicy.iidBernoulliVarianceProxy_eq]
    dsimp [logarithm]
    push_cast
    ring
  have hthresholdProduct :
      scale ^ 4 * logarithm <
        (episodes : Real) * (2 * visitFloor ^ 2) := by
    have hdenominator : 0 < 2 * visitFloor ^ 2 := by positivity
    exact (div_lt_iff₀ hdenominator).mp (by
      simpa [selfConsistentCountShrinkEpisodeThreshold, logarithm]
        using hthreshold)
  have hsquare :
      (scale ^ 2 * radius) ^ 2 <
        ((episodes : Real) * visitFloor) ^ 2 := by
    rw [mul_pow, hradiusSq]
    nlinarith
  have hscaled : scale ^ 2 * radius < (episodes : Real) * visitFloor :=
    (sq_lt_sq₀ (mul_nonneg (sq_nonneg scale) hradiusNonneg)
      (mul_nonneg hepisodesReal.le hvisitFloor.le)).mp hsquare
  exact (lt_div_iff₀ (sq_pos_of_pos hscale)).2 (by
    simpa [mul_comm] using hscaled)

/-- The reward threshold gives a half-scale-squared sampled-reward-sum bound. -/
theorem simultaneousRewardSumConfidenceRadius_lt_episodes_mul_visitFloor_div_two_scale_sq_of_threshold
    (mdp : MDP State Action) {rounds episodes : Nat}
    (varianceProxy : NNReal) {delta visitFloor scale : Real}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor)
    (hscale : 0 < scale)
    (hthreshold : selfConsistentRewardShrinkEpisodeThreshold mdp rounds
        varianceProxy delta visitFloor scale < (episodes : Real)) :
    MDP.MeanCompatibleRewardKernel.simultaneousRewardSumConfidenceRadius
        mdp episodes varianceProxy (multiBatchLocalDelta rounds delta) <
      (episodes : Real) * visitFloor / (2 * scale ^ 2) := by
  let witnessState : State := Classical.choice inferInstance
  let witnessAction : Action := Classical.choice inferInstance
  have hcoordinate : Nonempty (VisitCoordinate mdp) :=
    ⟨{ stage := ⟨0, hhorizon⟩, state := witnessState, action := witnessAction }⟩
  have hroundsReal : (0 : Real) < rounds := by exact_mod_cast hrounds
  have hlocalPos : 0 < multiBatchLocalDelta rounds delta :=
    div_pos hdelta hroundsReal
  have hlocalLeOne : multiBatchLocalDelta rounds delta <= 1 :=
    (div_le_self hdelta.le (by exact_mod_cast hrounds)).trans hdelta_le_one
  have hcoordinatePos :
      0 < MDP.MeanCompatibleRewardKernel.simultaneousRewardDelta mdp
        (multiBatchLocalDelta rounds delta) :=
    MDP.MeanCompatibleRewardKernel.simultaneousRewardDelta_pos
      mdp hcoordinate hlocalPos
  have hcoordinateLeOne :
      MDP.MeanCompatibleRewardKernel.simultaneousRewardDelta mdp
        (multiBatchLocalDelta rounds delta) <= 1 :=
    MDP.MeanCompatibleRewardKernel.simultaneousRewardDelta_le_one
      mdp hcoordinate hlocalPos hlocalLeOne
  let radius :=
    MDP.MeanCompatibleRewardKernel.simultaneousRewardSumConfidenceRadius
      mdp episodes varianceProxy (multiBatchLocalDelta rounds delta)
  let logarithm := Real.log
    (2 / MDP.MeanCompatibleRewardKernel.simultaneousRewardDelta mdp
      (multiBatchLocalDelta rounds delta))
  have hepisodesReal : (0 : Real) < episodes := by exact_mod_cast hepisodes
  have hradiusNonneg : 0 <= radius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hradiusSq :
      radius ^ 2 = 2 * (episodes : Real) * (varianceProxy : Real) * logarithm := by
    change
      (Concentration.subGaussianSumConfidenceRadius
          ((episodes : NNReal) * varianceProxy)
          (MDP.MeanCompatibleRewardKernel.simultaneousRewardDelta mdp
            (multiBatchLocalDelta rounds delta))) ^ 2 =
        2 * (episodes : Real) * (varianceProxy : Real) * logarithm
    rw [Concentration.subGaussianSumConfidenceRadius_sq _ _
      hcoordinatePos hcoordinateLeOne]
    dsimp [logarithm]
    push_cast
    ring
  have hthresholdProduct :
      8 * (varianceProxy : Real) * logarithm * scale ^ 4 <
        (episodes : Real) * visitFloor ^ 2 := by
    have hdenominator : 0 < visitFloor ^ 2 := sq_pos_of_pos hvisitFloor
    exact (div_lt_iff₀ hdenominator).mp (by
      simpa [selfConsistentRewardShrinkEpisodeThreshold, logarithm]
        using hthreshold)
  have hsquare :
      (2 * scale ^ 2 * radius) ^ 2 <
        ((episodes : Real) * visitFloor) ^ 2 := by
    rw [mul_pow, mul_pow, hradiusSq]
    nlinarith
  have hscaled :
      2 * scale ^ 2 * radius < (episodes : Real) * visitFloor :=
    (sq_lt_sq₀
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg scale)) hradiusNonneg)
      (mul_nonneg hepisodesReal.le hvisitFloor.le)).mp hsquare
  exact (lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hscale))).2 (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled)

namespace AdaptiveStochasticEpisodeBatchSource

/-- Maximum of calibration, count-shrinkage, and reward-shrinkage thresholds. -/
noncomputable def selfConsistentScheduledEpisodeThreshold
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  max
    (exploratoryPathCalibrationEpisodeThreshold mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
      (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
        mdp baseVisitFloor n))
    (max
      (selfConsistentCountShrinkEpisodeThreshold mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
        (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
          mdp baseVisitFloor n)
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real))
      (selfConsistentRewardShrinkEpisodeThreshold mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        varianceProxy
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
        (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
          mdp baseVisitFloor n)
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real)))

/-- Positive natural episode count one step above the explicit maximum threshold. -/
noncomputable def selfConsistentScheduledEpisodes
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Nat :=
  Nat.ceil (selfConsistentScheduledEpisodeThreshold mdp varianceProxy
    baseVisitFloor n) + 1

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledEpisodes_pos
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    0 < selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n := by
  unfold selfConsistentScheduledEpisodes
  omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledEpisodeThreshold_lt_episodes
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    selfConsistentScheduledEpisodeThreshold mdp varianceProxy baseVisitFloor n <
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n : Real) := by
  have hceil : selfConsistentScheduledEpisodeThreshold mdp varianceProxy
      baseVisitFloor n <=
      (Nat.ceil (selfConsistentScheduledEpisodeThreshold mdp varianceProxy
        baseVisitFloor n) : Real) := Nat.le_ceil _
  unfold selfConsistentScheduledEpisodes
  push_cast
  linarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled episode count strictly exceeds the path-calibration threshold. -/
theorem exploratoryPathCalibrationEpisodeThreshold_lt_selfConsistentScheduledEpisodes
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    exploratoryPathCalibrationEpisodeThreshold mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
        (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
          mdp baseVisitFloor n) <
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n : Real) := by
  exact (le_max_left _ _).trans_lt
    (selfConsistentScheduledEpisodeThreshold_lt_episodes
      mdp varianceProxy baseVisitFloor n)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- The scheduled episode count strictly exceeds the count-shrink threshold. -/
theorem selfConsistentCountShrinkEpisodeThreshold_lt_scheduledEpisodes
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    selfConsistentCountShrinkEpisodeThreshold mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
        (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
          mdp baseVisitFloor n)
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) <
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n : Real) := by
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt
    (selfConsistentScheduledEpisodeThreshold_lt_episodes
      mdp varianceProxy baseVisitFloor n)

/-- The scheduled episode count strictly exceeds the sampled-reward shrink threshold. -/
theorem selfConsistentRewardShrinkEpisodeThreshold_lt_scheduledEpisodes
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    selfConsistentRewardShrinkEpisodeThreshold mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        varianceProxy
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
        (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
          mdp baseVisitFloor n)
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) <
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n : Real) := by
  exact ((le_max_right _ _).trans (le_max_right _ _)).trans_lt
    (selfConsistentScheduledEpisodeThreshold_lt_episodes
      mdp varianceProxy baseVisitFloor n)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- The explicit schedule discharges the strict count margin and half contraction. -/
theorem selfConsistentScheduled_countMargin_and_halfContraction
    (mdp : MDP State Action) (witnessState : State)
    (varianceProxy : NNReal) {baseVisitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    simultaneousCountConfidenceRadius mdp
        (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
        (multiBatchLocalDelta
          (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
          (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)) <
        (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n : Real) *
          AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
            mdp baseVisitFloor n /\
      uniformFloorStochasticTransitionContraction mdp
          (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
          (multiBatchLocalDelta
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n))
          (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
            mdp baseVisitFloor n) <= 1 / 2 := by
  exact episodeThreshold_countMargin_and_halfContraction mdp witnessState
    hhorizon
    (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
    (selfConsistentScheduledEpisodes_pos mdp varianceProxy baseVisitFloor n)
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
    (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
      mdp hbaseVisitFloor n)
    (exploratoryPathCalibrationEpisodeThreshold_lt_selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor n)

/-- Shared per-round confidence share for the self-consistent schedule. -/
noncomputable def selfConsistentScheduledLocalDelta
    (mdp : MDP State Action) (n : Nat) : Real :=
  multiBatchLocalDelta
    (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)

/-- Actual sampled-reward coordinate budget under the explicit schedule. -/
noncomputable def selfConsistentScheduledRewardBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  uniformFloorStochasticRewardCoordinateRadius mdp
    (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
    varianceProxy (selfConsistentScheduledLocalDelta mdp n)
    (selfConsistentScheduledLocalDelta mdp n)
    (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n)

/-- Actual transition contraction under the explicit schedule. -/
noncomputable def selfConsistentScheduledTransitionContraction
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  uniformFloorStochasticTransitionContraction mdp
    (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
    (selfConsistentScheduledLocalDelta mdp n)
    (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n)

/-- Exact fixed-point transition budget under the explicit schedule. -/
noncomputable def selfConsistentScheduledTransitionBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  uniformFloorStochasticSelfConsistentTransitionBudget mdp
    (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
    (selfConsistentScheduledLocalDelta mdp n)
    (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n) 1
    (selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor n)

/-- Scheduled count confidence is smaller than visit mass divided by `scale^2`. -/
theorem selfConsistentScheduledCountRadius_lt_mass_div_scale_sq
    (mdp : MDP State Action) (varianceProxy : NNReal) {baseVisitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    simultaneousCountConfidenceRadius mdp
        (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
        (selfConsistentScheduledLocalDelta mdp n) <
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n : Real) *
          AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
            mdp baseVisitFloor n /
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2 := by
  exact
    simultaneousCountConfidenceRadius_lt_episodes_mul_visitFloor_div_scale_sq_of_threshold
      mdp hhorizon
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
      (selfConsistentScheduledEpisodes_pos mdp varianceProxy baseVisitFloor n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
      (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
        mdp hbaseVisitFloor n)
      (by
        exact_mod_cast AdaptiveEpisodeBatchSource.decayingExplorationScale_pos n)
      (selfConsistentCountShrinkEpisodeThreshold_lt_scheduledEpisodes
        mdp varianceProxy baseVisitFloor n)

/-- Scheduled reward-sum confidence is smaller than visit mass divided by `2*scale^2`. -/
theorem selfConsistentScheduledRewardSumRadius_lt_mass_div_two_scale_sq
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    MDP.MeanCompatibleRewardKernel.simultaneousRewardSumConfidenceRadius mdp
        (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
        varianceProxy (selfConsistentScheduledLocalDelta mdp n) <
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n : Real) *
          AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
            mdp baseVisitFloor n /
        (2 * (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2) := by
  exact
    simultaneousRewardSumConfidenceRadius_lt_episodes_mul_visitFloor_div_two_scale_sq_of_threshold
      mdp varianceProxy hhorizon
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
      (selfConsistentScheduledEpisodes_pos mdp varianceProxy baseVisitFloor n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
      (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
        mdp hbaseVisitFloor n)
      (by
        exact_mod_cast AdaptiveEpisodeBatchSource.decayingExplorationScale_pos n)
      (selfConsistentRewardShrinkEpisodeThreshold_lt_scheduledEpisodes
        mdp varianceProxy baseVisitFloor n)

/-- A simple deterministic envelope for the scheduled transition contraction. -/
noncomputable def selfConsistentScheduledTransitionContractionEnvelope
    (mdp : MDP State Action) (n : Nat) : Real :=
  (4 * (Fintype.card State : Real) * (mdp.horizon : Real)) /
    (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2

/-- The scheduled sampled-reward budget is nonnegative. -/
theorem selfConsistentScheduledRewardBudget_nonneg
    (mdp : MDP State Action) (witnessState : State)
    (varianceProxy : NNReal) {baseVisitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    0 <= selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor n := by
  exact uniformFloorStochasticRewardCoordinateRadius_nonneg
    (selfConsistentScheduled_countMargin_and_halfContraction mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n).1

/-- The scheduled sampled-reward budget is strictly below `scale^-2`. -/
theorem selfConsistentScheduledRewardBudget_lt_inv_scale_sq
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor n <
      1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2 := by
  let episodes := selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n
  let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
    mdp baseVisitFloor n
  let scale : Real := AdaptiveEpisodeBatchSource.decayingExplorationScale n
  let countRadius := simultaneousCountConfidenceRadius mdp episodes
    (selfConsistentScheduledLocalDelta mdp n)
  let rewardRadius :=
    MDP.MeanCompatibleRewardKernel.simultaneousRewardSumConfidenceRadius mdp
      episodes varianceProxy (selfConsistentScheduledLocalDelta mdp n)
  let mass := (episodes : Real) * visitFloor
  have hepisodesPos : 0 < episodes :=
    selfConsistentScheduledEpisodes_pos mdp varianceProxy baseVisitFloor n
  have hvisitFloorPos : 0 < visitFloor :=
    AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
      mdp hbaseVisitFloor n
  have hmassPos : 0 < mass := by
    exact mul_pos (by exact_mod_cast hepisodesPos) hvisitFloorPos
  have hscalePos : 0 < scale := by
    dsimp [scale]
    exact_mod_cast AdaptiveEpisodeBatchSource.decayingExplorationScale_pos n
  have hscaleFour : 4 <= scale ^ 2 := by
    have hscaleTwo : 2 <= scale := by
      simp [scale, AdaptiveEpisodeBatchSource.decayingExplorationScale]
    nlinarith
  have hcountNonneg : 0 <= countRadius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hrewardNonneg : 0 <= rewardRadius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hcount := selfConsistentScheduledCountRadius_lt_mass_div_scale_sq
    mdp varianceProxy hhorizon hbaseVisitFloor n
  change countRadius < mass / scale ^ 2 at hcount
  have hreward := selfConsistentScheduledRewardSumRadius_lt_mass_div_two_scale_sq
    mdp varianceProxy hhorizon hbaseVisitFloor n
  change rewardRadius < mass / (2 * scale ^ 2) at hreward
  have hcountScaled : countRadius * scale ^ 2 < mass :=
    (lt_div_iff₀ (sq_pos_of_pos hscalePos)).mp hcount
  have hcountQuarter : 4 * countRadius < mass := by
    exact (mul_le_mul_of_nonneg_right hscaleFour hcountNonneg).trans_lt
      (by simpa [mul_comm] using hcountScaled)
  have hrewardScaled : rewardRadius * (2 * scale ^ 2) < mass :=
    (lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hscalePos))).mp hreward
  have hdenominatorPos : 0 < mass - countRadius := by nlinarith
  unfold selfConsistentScheduledRewardBudget
  unfold uniformFloorStochasticRewardCoordinateRadius
  change rewardRadius / (mass - countRadius) < 1 / scale ^ 2
  rw [div_lt_iff₀ hdenominatorPos]
  rw [show 1 / scale ^ 2 * (mass - countRadius) =
      (mass - countRadius) / scale ^ 2 by ring]
  rw [lt_div_iff₀ (sq_pos_of_pos hscalePos)]
  nlinarith

/-- The scheduled transition contraction is nonnegative. -/
theorem selfConsistentScheduledTransitionContraction_nonneg
    (mdp : MDP State Action) (witnessState : State)
    (varianceProxy : NNReal) {baseVisitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    0 <= selfConsistentScheduledTransitionContraction mdp varianceProxy
      baseVisitFloor n := by
  exact uniformFloorStochasticTransitionContraction_nonneg
    (selfConsistentScheduled_countMargin_and_halfContraction mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n).1

/-- The scheduled transition contraction is bounded by its `scale^-2` envelope. -/
theorem selfConsistentScheduledTransitionContraction_lt_envelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    selfConsistentScheduledTransitionContraction mdp varianceProxy
        baseVisitFloor n <
      selfConsistentScheduledTransitionContractionEnvelope mdp n := by
  let episodes := selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n
  let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
    mdp baseVisitFloor n
  let scale : Real := AdaptiveEpisodeBatchSource.decayingExplorationScale n
  let countRadius := simultaneousCountConfidenceRadius mdp episodes
    (selfConsistentScheduledLocalDelta mdp n)
  let mass := (episodes : Real) * visitFloor
  have hepisodesPos : 0 < episodes :=
    selfConsistentScheduledEpisodes_pos mdp varianceProxy baseVisitFloor n
  have hvisitFloorPos : 0 < visitFloor :=
    AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
      mdp hbaseVisitFloor n
  have hmassPos : 0 < mass := by
    exact mul_pos (by exact_mod_cast hepisodesPos) hvisitFloorPos
  have hscalePos : 0 < scale := by
    dsimp [scale]
    exact_mod_cast AdaptiveEpisodeBatchSource.decayingExplorationScale_pos n
  have hscaleFour : 4 <= scale ^ 2 := by
    have hscaleTwo : 2 <= scale := by
      simp [scale, AdaptiveEpisodeBatchSource.decayingExplorationScale]
    nlinarith
  have hcountNonneg : 0 <= countRadius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hcount := selfConsistentScheduledCountRadius_lt_mass_div_scale_sq
    mdp varianceProxy hhorizon hbaseVisitFloor n
  change countRadius < mass / scale ^ 2 at hcount
  have hcountScaled : countRadius * scale ^ 2 < mass :=
    (lt_div_iff₀ (sq_pos_of_pos hscalePos)).mp hcount
  have hcountQuarter : 4 * countRadius < mass := by
    exact (mul_le_mul_of_nonneg_right hscaleFour hcountNonneg).trans_lt
      (by simpa [mul_comm] using hcountScaled)
  have hdenominatorPos : 0 < mass - countRadius := by nlinarith
  have hcoordinate :
      uniformFloorTransitionCoordinateRadius mdp episodes
          (selfConsistentScheduledLocalDelta mdp n) visitFloor <
        4 / scale ^ 2 := by
    unfold uniformFloorTransitionCoordinateRadius
    change 2 * countRadius / (mass - countRadius) < 4 / scale ^ 2
    rw [div_lt_iff₀ hdenominatorPos]
    rw [show 4 / scale ^ 2 * (mass - countRadius) =
        (4 * (mass - countRadius)) / scale ^ 2 by ring]
    rw [lt_div_iff₀ (sq_pos_of_pos hscalePos)]
    nlinarith
  have hcoefficient :
      0 < (Fintype.card State : Real) * (mdp.horizon : Real) := by
    positivity
  have hscaled := mul_lt_mul_of_pos_right hcoordinate hcoefficient
  change (Fintype.card State : Real) *
        uniformFloorTransitionCoordinateRadius mdp episodes
          (selfConsistentScheduledLocalDelta mdp n) visitFloor *
          (mdp.horizon : Real) <
      selfConsistentScheduledTransitionContractionEnvelope mdp n
  calc
    (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes
            (selfConsistentScheduledLocalDelta mdp n) visitFloor *
            (mdp.horizon : Real) =
        uniformFloorTransitionCoordinateRadius mdp episodes
            (selfConsistentScheduledLocalDelta mdp n) visitFloor *
          ((Fintype.card State : Real) * (mdp.horizon : Real)) := by ring
    _ < (4 / scale ^ 2) *
          ((Fintype.card State : Real) * (mdp.horizon : Real)) := hscaled
    _ = selfConsistentScheduledTransitionContractionEnvelope mdp n := by
      unfold selfConsistentScheduledTransitionContractionEnvelope
      dsimp [scale]
      ring

/-- The calibration half bound makes the scheduled contraction strictly smaller than one. -/
theorem selfConsistentScheduledTransitionContraction_lt_one
    (mdp : MDP State Action) (witnessState : State)
    (varianceProxy : NNReal) {baseVisitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    selfConsistentScheduledTransitionContraction mdp varianceProxy
      baseVisitFloor n < 1 := by
  have hhalf :=
    (selfConsistentScheduled_countMargin_and_halfContraction mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n).2
  change selfConsistentScheduledTransitionContraction mdp varianceProxy
    baseVisitFloor n <= 1 / 2 at hhalf
  linarith

/-- The exact scheduled transition budget is nonnegative. -/
theorem selfConsistentScheduledTransitionBudget_nonneg
    (mdp : MDP State Action) (witnessState : State)
    (varianceProxy : NNReal) {baseVisitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    0 <= selfConsistentScheduledTransitionBudget mdp varianceProxy
      baseVisitFloor n := by
  exact uniformFloorStochasticSelfConsistentTransitionBudget_nonneg
    (selfConsistentScheduled_countMargin_and_halfContraction mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n).1
    (by norm_num)
    (selfConsistentScheduledRewardBudget_nonneg mdp witnessState varianceProxy
      hhorizon hbaseVisitFloor n)
    (selfConsistentScheduledTransitionContraction_lt_one mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The square of the decaying-exploration scale tends to infinity. -/
theorem decayingExplorationScale_sq_tendsto_atTop :
    Tendsto
      (fun n : Nat =>
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2)
      atTop atTop := by
  have hscale : Tendsto
      (fun n : Nat =>
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real))
      atTop atTop := by
    change Tendsto (fun n : Nat => (((n + 2 : Nat) : Real))) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  exact (tendsto_pow_atTop (α := Real) (by norm_num : (2 : Nat) ≠ 0)).comp hscale

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The deterministic contraction envelope tends to zero. -/
theorem selfConsistentScheduledTransitionContractionEnvelope_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto (selfConsistentScheduledTransitionContractionEnvelope mdp)
      atTop (nhds 0) := by
  unfold selfConsistentScheduledTransitionContractionEnvelope
  exact tendsto_const_nhds.div_atTop decayingExplorationScale_sq_tendsto_atTop

/-- The actual scheduled sampled-reward budget tends to zero. -/
theorem selfConsistentScheduledRewardBudget_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor)
      atTop (nhds 0) := by
  let witnessState : State := Classical.choice inferInstance
  apply squeeze_zero
  · intro n
    exact selfConsistentScheduledRewardBudget_nonneg mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n
  · intro n
    exact (selfConsistentScheduledRewardBudget_lt_inv_scale_sq mdp
      varianceProxy hhorizon hbaseVisitFloor n).le
  · exact tendsto_const_nhds.div_atTop decayingExplorationScale_sq_tendsto_atTop

/-- The actual scheduled transition contraction tends to zero. -/
theorem selfConsistentScheduledTransitionContraction_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledTransitionContraction mdp varianceProxy
        baseVisitFloor)
      atTop (nhds 0) := by
  let witnessState : State := Classical.choice inferInstance
  apply squeeze_zero
  · intro n
    exact selfConsistentScheduledTransitionContraction_nonneg mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n
  · intro n
    exact (selfConsistentScheduledTransitionContraction_lt_envelope mdp
      varianceProxy hhorizon hbaseVisitFloor n).le
  · exact selfConsistentScheduledTransitionContractionEnvelope_tendsto_zero mdp

/-- The exact fixed-point transition budget tends to zero with its contraction. -/
theorem selfConsistentScheduledTransitionBudget_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledTransitionBudget mdp varianceProxy baseVisitFloor)
      atTop (nhds 0) := by
  have hreward := selfConsistentScheduledRewardBudget_tendsto_zero mdp
    varianceProxy hhorizon hbaseVisitFloor
  have hq := selfConsistentScheduledTransitionContraction_tendsto_zero mdp
    varianceProxy hhorizon hbaseVisitFloor
  have hbase : Tendsto
      (fun n => 1 + 2 *
        selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor n)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hreward)
  have hnumerator : Tendsto
      (fun n =>
        selfConsistentScheduledTransitionContraction mdp varianceProxy
            baseVisitFloor n *
          (1 + 2 * selfConsistentScheduledRewardBudget mdp varianceProxy
            baseVisitFloor n))
      atTop (nhds 0) := by
    simpa using hq.mul hbase
  have hdenominator : Tendsto
      (fun n => 1 - selfConsistentScheduledTransitionContraction mdp
        varianceProxy baseVisitFloor n)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hq
  unfold selfConsistentScheduledTransitionBudget
    uniformFloorStochasticSelfConsistentTransitionBudget
    selfConsistentTransitionBudget
  simpa [selfConsistentScheduledTransitionContraction] using
    hnumerator.div hdenominator (by norm_num)

/-- Planning part of the scheduled self-consistent realized certificate. -/
noncomputable def selfConsistentScheduledPlanningAverageRegretBound
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  adaptiveStochasticSampledEmpiricalOptimisticSelfConsistentBudgetAverageBound
    mdp (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
    (selfConsistentScheduledLocalDelta mdp n)
    (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n)
    (AdaptiveEpisodeBatchSource.decayingExplorationRate n) 1
    (selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor n)

/-- Full realized successor-average regret bound under the explicit schedule. -/
noncomputable def selfConsistentScheduledRealizedSuccessorAverageRegretBound
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  selfConsistentScheduledPlanningAverageRegretBound mdp varianceProxy
      baseVisitFloor n +
    normalizedSuccessorGlobalReturnConfidenceRadius mdp
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
      1 varianceProxy
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)

/-- Count, reward, and globally centered return events each consume one share. -/
noncomputable def selfConsistentScheduledRealizedFailureBudget (n : Nat) : ENNReal :=
  (ENNReal.ofReal (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) +
    ENNReal.ofReal (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)) +
  ENNReal.ofReal (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)

/-- The scheduled planning average-regret bound tends to zero. -/
theorem selfConsistentScheduledPlanningAverageRegretBound_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledPlanningAverageRegretBound mdp varianceProxy
        baseVisitFloor)
      atTop (nhds 0) := by
  have hreward := selfConsistentScheduledRewardBudget_tendsto_zero mdp
    varianceProxy hhorizon hbaseVisitFloor
  have htransition := selfConsistentScheduledTransitionBudget_tendsto_zero mdp
    varianceProxy hhorizon hbaseVisitFloor
  have hsum : Tendsto
      (fun n => selfConsistentScheduledRewardBudget mdp varianceProxy
          baseVisitFloor n +
        selfConsistentScheduledTransitionBudget mdp varianceProxy
          baseVisitFloor n)
      atTop (nhds 0) := by
    simpa using hreward.add htransition
  have hplanning : Tendsto
      (fun n => (mdp.horizon : Real) *
        (2 * (selfConsistentScheduledRewardBudget mdp varianceProxy
            baseVisitFloor n +
          selfConsistentScheduledTransitionBudget mdp varianceProxy
            baseVisitFloor n)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.mul hsum)
  unfold selfConsistentScheduledPlanningAverageRegretBound
    adaptiveStochasticSampledEmpiricalOptimisticSelfConsistentBudgetAverageBound
  simpa [selfConsistentScheduledTransitionBudget,
    AdaptiveEpisodeBatchSource.decayingExplorationRate] using
    hplanning.add
      (AdaptiveEpisodeBatchSource.decayingExplorationBehaviorCharge_tendsto_zero mdp)

/-- The scheduled globally centered return radius tends to zero. -/
theorem selfConsistentScheduledNormalizedSuccessorGlobalReturnRadius_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (fun n => normalizedSuccessorGlobalReturnConfidenceRadius mdp
        (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        1 varianceProxy
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact normalizedSuccessorGlobalReturnConfidenceRadius_nonneg _ _ _ _ _ _
  · intro n
    exact normalizedSuccessorGlobalReturnConfidenceRadius_le_decayingEnvelope
      mdp (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
      1 varianceProxy n
      (selfConsistentScheduledEpisodes_pos mdp varianceProxy baseVisitFloor n)
  · exact decayingExplorationStochasticReturnRadiusEnvelope_tendsto_zero
      mdp 1 varianceProxy

/-- The full scheduled realized successor-average bound tends to zero. -/
theorem selfConsistentScheduledRealizedSuccessorAverageRegretBound_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledRealizedSuccessorAverageRegretBound mdp
        varianceProxy baseVisitFloor)
      atTop (nhds 0) := by
  unfold selfConsistentScheduledRealizedSuccessorAverageRegretBound
  simpa only [add_zero] using
    (selfConsistentScheduledPlanningAverageRegretBound_tendsto_zero mdp
      varianceProxy hhorizon hbaseVisitFloor).add
    (selfConsistentScheduledNormalizedSuccessorGlobalReturnRadius_tendsto_zero
      mdp varianceProxy baseVisitFloor)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The three-share failure budget tends to zero. -/
theorem selfConsistentScheduledRealizedFailureBudget_tendsto_zero :
    Tendsto selfConsistentScheduledRealizedFailureBudget atTop (nhds 0) := by
  unfold selfConsistentScheduledRealizedFailureBudget
  simpa only [zero_add, add_zero] using
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_ennreal_tendsto_zero.add
      AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_ennreal_tendsto_zero).add
    AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_ennreal_tendsto_zero

/-- Failure probability and realized-regret certificates vanish together. -/
theorem selfConsistentScheduledFailureAndRealizedBound_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (fun n =>
        (selfConsistentScheduledRealizedFailureBudget n,
          selfConsistentScheduledRealizedSuccessorAverageRegretBound mdp
            varianceProxy baseVisitFloor n))
      atTop (nhds (0, 0)) := by
  rw [nhds_prod_eq]
  exact selfConsistentScheduledRealizedFailureBudget_tendsto_zero.prodMk
    (selfConsistentScheduledRealizedSuccessorAverageRegretBound_tendsto_zero
      mdp varianceProxy hhorizon hbaseVisitFloor)

end AdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/--
At every schedule index, actual sampled count/reward confidence, optimism, and
globally centered realized successor-average regret hold outside three finite
bad-event shares.  The episode and trajectory spaces may change with `n`.
-/
theorem exploratorySource_trajectoryMeasure_selfConsistentScheduled_allCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real) (n : Nat)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp) (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
    let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
    let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
    let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n
    let episodes :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor n
    let localDelta :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp n
    let rewardBudget :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor n
    let transitionBudget :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor n
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
    let modelBadEvent := source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy delta delta
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds 1 varianceProxy delta
    let combinedBadEvent := modelBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureBudget n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
              defaultState rewardBudget transitionBudget round).upperValueRemaining
                mdp.horizon le_rfl state) /\
          source.realizedSuccessorAverageRegret trajectory rounds <=
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretBound
              mdp varianceProxy baseVisitFloor n := by
  dsimp only
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
  let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
    mdp baseVisitFloor n
  let episodes :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor n
  let localDelta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp n
  let rewardBudget :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor n
  let transitionBudget :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor n
  let source := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState rewardBudget transitionBudget explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  let modelBadEvent := source.adaptiveAllCoordinateEmpiricalModelBadEvent
    rounds varianceProxy delta delta
  let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
    rounds 1 varianceProxy delta
  let combinedBadEvent := modelBadEvent ∪ returnBadEvent
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor n
  have hdelta : 0 < delta :=
    AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n
  have hdelta_le_one : delta <= 1 :=
    AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n
  have hfloor : ExploratoryPathUniformVisitFloor support explorationRate
      visitFloor :=
    AdaptiveEpisodeBatchSource.decayingExplorationUniformVisitFloor
      support hbaseFloor n
  have hcalibration :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduled_countMargin_and_halfContraction
      mdp defaultState varianceProxy hhorizon hbaseVisitFloor n
  have hmargin : simultaneousCountConfidenceRadius mdp episodes localDelta <
      (episodes : Real) * visitFloor := by
    simpa [episodes, localDelta, visitFloor] using hcalibration.1
  have hq : uniformFloorStochasticTransitionContraction mdp episodes
      localDelta visitFloor < 1 := by
    simpa [episodes, localDelta, visitFloor] using
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionContraction_lt_one
        mdp defaultState varianceProxy hhorizon hbaseVisitFloor n
  have hmodelTotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)) := by
    positivity
  have hreturnTotal : 0 <
      ((AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp rounds episodes 1 varianceProxy : NNReal) : Real) := by
    rw [AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy_coe]
    have hbase : 0 <
        mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy :=
      mdp.globalReturnDeviationPerEpisodeVarianceProxy_pos 1 varianceProxy
        (by norm_num) hhorizon
    positivity
  have hparent :=
    exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_selfConsistentBudgetRealizedSuccessorAverageRegret_of_pathSupport_selfConsistentCalibration
      rewardSource initialTable explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
      rounds hrounds hepisodes varianceProxy law hmodelTotal
      delta hdelta hdelta_le_one delta hdelta hdelta_le_one
      delta hdelta hdelta_le_one defaultState 1 hrewardBound
      support visitFloor hfloor hmargin hq hreturnTotal
  simpa [rounds, delta, explorationRate, visitFloor, episodes, localDelta,
    rewardBudget, transitionBudget, source, modelBadEvent, returnBadEvent,
    combinedBadEvent,
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureBudget,
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretBound,
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledPlanningAverageRegretBound,
    AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius,
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget,
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget,
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta] using hparent

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
