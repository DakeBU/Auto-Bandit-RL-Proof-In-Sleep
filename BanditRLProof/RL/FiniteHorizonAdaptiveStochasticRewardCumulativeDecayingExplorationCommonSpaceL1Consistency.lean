import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceConsistency
import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceL1Consistency

/-!
# Stochastic common-space L1 realized-behavior consistency

This module strengthens the scheduled stochastic-reward common-space theorem
from convergence in probability to convergence of the expected absolute
realized-behavior regret and then to convergence in `L1`.

Sampled rewards remain unbounded.  The deterministic `2H` envelope is used
only for selected-policy expected regret, whose values are computed from the
bounded mean-reward MDP.  The globally centered sampled-return deviation is
integrated through its compiled sub-Gaussian MGF at the scaled tilt
`1 / sqrt(proxy)`.
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

namespace MarkovPolicy

/-- Mean-reward expected regret has the deterministic `2H` envelope. -/
theorem expectedRegret_le_two_mul_horizon_of_rewardBound
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    policy.expectedRegret initialState <= 2 * (mdp.horizon : Real) := by
  have hoptimal :=
    AdaptiveEpisodeBatchSource.abs_optimalInitialExpectedReturn_le_horizon
      mdp initialState hrewardBound
  have hpolicy :
      |integral (policy.trajectoryMeasure initialState) mdp.cumulativeReward| <=
        (mdp.horizon : Real) := by
    rw [← Real.norm_eq_abs]
    have hnorm := norm_integral_le_of_norm_le_const
      (μ := policy.trajectoryMeasure initialState)
      (C := (mdp.horizon : Real))
      (Filter.Eventually.of_forall fun trajectory => by
        rw [Real.norm_eq_abs]
        exact mdp.abs_cumulativeReward_le_horizon hrewardBound trajectory)
    simpa using hnorm
  unfold expectedRegret
  calc
    integral initialState
          (mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon)) -
        integral (policy.trajectoryMeasure initialState) mdp.cumulativeReward <=
      |integral initialState
          (mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon))| +
        |integral (policy.trajectoryMeasure initialState)
          mdp.cumulativeReward| := by
        have hleft := le_abs_self
          (integral initialState
            (mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon)))
        have hright := neg_le_abs
          (integral (policy.trajectoryMeasure initialState)
            mdp.cumulativeReward)
        linarith
    _ <= (mdp.horizon : Real) + (mdp.horizon : Real) :=
      add_le_add hoptimal hpolicy
    _ = 2 * (mdp.horizon : Real) := by ring

end MarkovPolicy

namespace AdaptiveStochasticEpisodeBatchSource

/-- Every selected-policy expected successor average is at most `2H`. -/
theorem successorExpectedAverageRegret_le_two_mul_horizon
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    source.successorExpectedAverageRegret trajectory rounds <=
      2 * (mdp.horizon : Real) := by
  have hsum :
      source.successorExpectedCumulativeRegret trajectory rounds <=
        ∑ _round : Fin rounds, 2 * (mdp.horizon : Real) := by
    unfold successorExpectedCumulativeRegret
    exact Finset.sum_le_sum fun round _ =>
      MarkovPolicy.expectedRegret_le_two_mul_horizon_of_rewardBound
        (source.successorPolicyAt trajectory round) initialState hrewardBound
  have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
  unfold successorExpectedAverageRegret
  calc
    source.successorExpectedCumulativeRegret trajectory rounds /
        (rounds : Real) <=
      (∑ _round : Fin rounds, 2 * (mdp.horizon : Real)) /
        (rounds : Real) := div_le_div_of_nonneg_right hsum hroundsReal.le
    _ = 2 * (mdp.horizon : Real) := by
      simp
      field_simp

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/--
The cumulative globally centered successor deviation inherits one global
sub-Gaussian MGF from the strongly adapted conditional increments.
-/
theorem trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_hasSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (source.cumulativeSuccessorGlobalReturnDeviation rounds)
      (cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let F := Filtration.piLE
    (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | _ + 1 =>
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          episodes rewardBound rewardVarianceProxy
  have hadapted : StronglyAdapted F source.successorGlobalReturnIncrement := by
    simpa [F] using source.successorGlobalReturnIncrement_stronglyAdapted_piLE
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (source.successorGlobalReturnIncrement 0) (cY 0)
      source.trajectoryMeasure := by
    change ProbabilityTheory.HasSubgaussianMGF (fun _ => 0) 0
      source.trajectoryMeasure
    exact ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have hsucc : forall i, i < (rounds + 1) - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (source.successorGlobalReturnIncrement (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.successorGlobalReturnIncrement_succ_hasCondSubgaussianMGF
        i rewardBound rewardVarianceProxy hrewardBound law
  simpa [cumulativeSuccessorGlobalReturnDeviation,
    cumulativeSuccessorGlobalReturnVarianceProxy, cY] using
    (ProbabilityTheory.HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
      hadapted hzero (rounds + 1) hsucc)

/-- Finite-window stochastic realized successor-average regret is integrable. -/
theorem integrable_realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (hrewardBoundOne : forall state action,
      |mdp.reward state action| <= 1)
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    Integrable (fun trajectory =>
      source.realizedSuccessorAverageRegret trajectory rounds)
      source.trajectoryMeasure := by
  let expected := fun trajectory =>
    source.successorExpectedAverageRegret trajectory rounds
  let deviation := source.cumulativeSuccessorGlobalReturnDeviation rounds
  let denom := (episodes : Real) * (rounds : Real)
  have hdenom : 0 < denom := by
    dsimp [denom]
    positivity
  have hdeviation : Integrable deviation source.trajectoryMeasure :=
    (source.trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_hasSubgaussianMGF
      rounds rewardBound rewardVarianceProxy hrewardBound law).integrable
  have hrealizedMeas : Measurable (fun trajectory =>
      source.realizedSuccessorAverageRegret trajectory rounds) :=
    source.measurable_realizedSuccessorAverageRegret rounds
  have hexpectedMeas : Measurable expected := by
    have heq : expected = fun trajectory =>
        source.realizedSuccessorAverageRegret trajectory rounds +
          deviation trajectory / denom := by
      funext trajectory
      rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
        trajectory rounds hrounds hepisodes]
      simp [expected, deviation, denom]
    rw [heq]
    exact hrealizedMeas.add
      ((source.measurable_cumulativeSuccessorGlobalReturnDeviation rounds).div
        measurable_const)
  have hexpected : Integrable expected source.trajectoryMeasure := by
    apply Integrable.of_bound hexpectedMeas.aestronglyMeasurable
      (2 * (mdp.horizon : Real))
    exact Filter.Eventually.of_forall fun trajectory => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact source.successorExpectedAverageRegret_le_two_mul_horizon
          trajectory rounds hrounds hrewardBoundOne
      · exact source.successorExpectedAverageRegret_nonneg trajectory rounds
  have heq : (fun trajectory =>
      source.realizedSuccessorAverageRegret trajectory rounds) =
      fun trajectory => expected trajectory - deviation trajectory / denom := by
    funext trajectory
    exact source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
      trajectory rounds hrounds hepisodes
  rw [heq]
  exact hexpected.sub (hdeviation.div_const denom)

end AdaptiveStochasticEpisodeBatchSource

namespace AdaptiveCumulativeStochasticEmpiricalOptimisticSource

/-- The scaled-MGF first-moment contribution after episode/round normalization. -/
noncomputable def normalizedSuccessorGlobalReturnMGFFirstMomentBound
    (mdp : MDP State Action) (episodes rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : Real :=
  2 *
      Real.sqrt
        (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
          mdp rounds episodes rewardBound rewardVarianceProxy : Real) *
      Real.exp (1 / 2 : Real) /
    ((episodes : Real) * (rounds : Real))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scaled-MGF contribution is nonnegative. -/
theorem normalizedSuccessorGlobalReturnMGFFirstMomentBound_nonneg
    (mdp : MDP State Action) (episodes rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) :
    0 <= normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp episodes rounds
      rewardBound rewardVarianceProxy := by
  unfold normalizedSuccessorGlobalReturnMGFFirstMomentBound
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/--
Whenever `log (2/delta) >= 1/2`, the scaled-MGF first-moment term is at most
`2 * exp(1/2)` times the compiled normalized confidence radius.
-/
theorem normalizedSuccessorGlobalReturnMGFFirstMomentBound_le_confidenceRadius
    (mdp : MDP State Action) (episodes rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (delta : Real)
    (hepisodes : 0 < episodes) (hrounds : 0 < rounds)
    (hlog : (1 / 2 : Real) <= Real.log (2 / delta)) :
    normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp episodes rounds
        rewardBound rewardVarianceProxy <=
      2 * Real.exp (1 / 2 : Real) *
        AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
          mdp episodes rounds rewardBound rewardVarianceProxy delta := by
  let c : Real :=
    (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
      mdp rounds episodes rewardBound rewardVarianceProxy : Real)
  let denom : Real := (episodes : Real) * (rounds : Real)
  have hc : 0 <= c := by positivity
  have hdenom : 0 < denom := by
    dsimp [denom]
    positivity
  have hinside : c <= 2 * c * Real.log (2 / delta) := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hlog)]
  have hsqrt : Real.sqrt c <=
      Real.sqrt (2 * c * Real.log (2 / delta)) :=
    Real.sqrt_le_sqrt hinside
  unfold normalizedSuccessorGlobalReturnMGFFirstMomentBound
    AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
    Concentration.subGaussianSumConfidenceRadius
  dsimp [c, denom] at hsqrt hdenom ⊢
  calc
    2 * Real.sqrt
          (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp rounds episodes rewardBound rewardVarianceProxy : Real) *
          Real.exp (1 / 2 : Real) /
        ((episodes : Real) * (rounds : Real)) <=
      2 * Real.sqrt
          (2 *
            (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta)) *
          Real.exp (1 / 2 : Real) /
        ((episodes : Real) * (rounds : Real)) := by
      gcongr
    _ = 2 * Real.exp (1 / 2 : Real) *
        (Real.sqrt
          (2 *
            (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta)) /
          ((episodes : Real) * (rounds : Real))) := by ring

/-- The scheduled confidence logarithm is uniformly at least one half. -/
theorem one_half_le_log_two_div_vanishingAverageConfidenceDelta (n : Nat) :
    (1 / 2 : Real) <= Real.log
      (2 / AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) := by
  let scale : Real :=
    (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real)
  have hscaleTwo : 2 <= scale := by
    dsimp [scale, AdaptiveEpisodeBatchSource.decayingExplorationScale]
    norm_num
  have hrewrite :
      2 / AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n =
        2 * scale := by
    simp [scale, AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta,
      AdaptiveEpisodeBatchSource.decayingExplorationScale]
  have hlogFour : (1 / 2 : Real) <= Real.log 4 := by
    have h := Real.le_log_one_add_of_nonneg (show (0 : Real) <= 3 by norm_num)
    norm_num at h ⊢
    linarith
  rw [hrewrite]
  exact hlogFour.trans
    (Real.log_le_log (by norm_num : (0 : Real) < 4) (by nlinarith))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled scaled-MGF contribution tends to zero. -/
theorem decayingExplorationNormalizedSuccessorGlobalReturnMGFFirstMomentBound_tendsto_zero
    (mdp : MDP State Action) (baseVisitFloor : Real)
    (rewardBound rewardVarianceProxy : NNReal) :
    Tendsto
      (fun n => normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        rewardBound rewardVarianceProxy)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact normalizedSuccessorGlobalReturnMGFFirstMomentBound_nonneg
      mdp _ _ rewardBound rewardVarianceProxy
  · intro n
    exact normalizedSuccessorGlobalReturnMGFFirstMomentBound_le_confidenceRadius
      mdp _ _ rewardBound rewardVarianceProxy
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes_pos
        mdp baseVisitFloor n)
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
      (one_half_le_log_two_div_vanishingAverageConfidenceDelta n)
  · have hconst : Tendsto
        (fun _n : Nat => (2 * Real.exp (1 / 2 : Real))) atTop
        (nhds (2 * Real.exp (1 / 2 : Real))) := tendsto_const_nhds
    have h := hconst.mul
      (AdaptiveStochasticEpisodeBatchSource.decayingExplorationNormalizedSuccessorGlobalReturnRadius_tendsto_zero
        mdp baseVisitFloor rewardBound rewardVarianceProxy)
    simpa using
      (h : Tendsto
        (fun n => (2 * Real.exp (1 / 2 : Real)) *
          AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
            mdp
            (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
              mdp baseVisitFloor n)
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            rewardBound rewardVarianceProxy
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n))
        atTop (nhds ((2 * Real.exp (1 / 2 : Real)) * 0)))

/-- Scheduled cumulative sampled-return deviation on the stochastic common space. -/
noncomputable def decayingExplorationStochasticCumulativeReturnDeviationProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    DecayingExplorationStochasticWindowSpace mdp baseVisitFloor -> Real :=
  let source := decayingExplorationStochasticWindowSource mdp initialState
    rewardSource initialTable defaultState baseVisitFloor n
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  fun omega => source.cumulativeSuccessorGlobalReturnDeviation rounds (omega n)

/-- Every common-space cumulative deviation coordinate has its exact MGF. -/
theorem decayingExplorationStochasticCumulativeReturnDeviationProcess_hasSubgaussianMGF
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    ProbabilityTheory.HasSubgaussianMGF
      (decayingExplorationStochasticCumulativeReturnDeviationProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n)
      (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n) 1 rewardVarianceProxy)
      (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor) := by
  let source := decayingExplorationStochasticWindowSource mdp initialState
    rewardSource initialTable defaultState baseVisitFloor n
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, decayingExplorationStochasticWindowSource]
    infer_instance
  have hwindow :=
    source.trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_hasSubgaussianMGF
      rounds 1 rewardVarianceProxy hrewardBound law
  have hwindow' : ProbabilityTheory.HasSubgaussianMGF
      (source.cumulativeSuccessorGlobalReturnDeviation rounds)
      (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp rounds
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n) 1 rewardVarianceProxy)
      (decayingExplorationStochasticWindowMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor n) := by
    simpa [decayingExplorationStochasticWindowMeasure, source] using hwindow
  rw [← decayingExplorationStochasticCommonMeasure_map_eval mdp initialState
    rewardSource initialTable defaultState baseVisitFloor n] at hwindow'
  have hpull := ProbabilityTheory.HasSubgaussianMGF.of_map
    (μ := decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
      initialTable defaultState baseVisitFloor)
    (Y := fun omega : DecayingExplorationStochasticWindowSpace mdp
      baseVisitFloor => omega n)
    (X := source.cumulativeSuccessorGlobalReturnDeviation rounds)
    (measurable_pi_apply n).aemeasurable hwindow'
  simpa [decayingExplorationStochasticCumulativeReturnDeviationProcess,
    source, rounds, Function.comp_def,
    decayingExplorationStochasticWindowMeasure] using hpull

/-- Every scheduled common-space realized-regret coordinate is integrable. -/
theorem integrable_decayingExplorationStochasticRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    Integrable
      (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n)
      (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor) := by
  let source := decayingExplorationStochasticWindowSource mdp initialState
    rewardSource initialTable defaultState baseVisitFloor n
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    mdp baseVisitFloor n
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, decayingExplorationStochasticWindowSource]
    infer_instance
  have hwindow : Integrable
      (fun trajectory => source.realizedSuccessorAverageRegret trajectory rounds)
      (decayingExplorationStochasticWindowMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor n) := by
    simpa [decayingExplorationStochasticWindowMeasure, source, rounds, episodes]
      using source.integrable_realizedSuccessorAverageRegret rounds
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes_pos
          mdp baseVisitFloor n)
        1 rewardVarianceProxy hrewardBound hrewardBound law
  rw [← decayingExplorationStochasticCommonMeasure_map_eval mdp initialState
    rewardSource initialTable defaultState baseVisitFloor n] at hwindow
  have hpull := (integrable_map_measure hwindow.aestronglyMeasurable
    (measurable_pi_apply n).aemeasurable).1 hwindow
  simpa [decayingExplorationStochasticRealizedBehaviorRegretProcess,
    source, rounds, Function.comp_def] using hpull

/-- Pull only the projected-count failure event to the stochastic common space. -/
noncomputable def decayingExplorationStochasticCommonCountBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Set (DecayingExplorationStochasticWindowSpace mdp baseVisitFloor) :=
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
  (fun omega => omega n) ⁻¹'
    projectedAdaptiveCumulativeCountBadEvent
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        rounds delta

/-- The pulled-back projected-count event is measurable. -/
theorem measurableSet_decayingExplorationStochasticCommonCountBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    MeasurableSet
      (decayingExplorationStochasticCommonCountBadEvent mdp initialState
        initialTable defaultState baseVisitFloor n) := by
  have hfinite :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n rewardSource initialTable defaultState
        support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨hmeasurable, _htail, _houtside⟩
  unfold decayingExplorationStochasticCommonCountBadEvent
  dsimp only
  exact hmeasurable.preimage (measurable_pi_apply n)

/-- The common-space projected-count event consumes one confidence share. -/
theorem decayingExplorationStochasticCommonMeasure_countBadEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor
        (decayingExplorationStochasticCommonCountBadEvent mdp initialState
          initialTable defaultState baseVisitFloor n) <=
      ENNReal.ofReal
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) := by
  have hfinite :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n rewardSource initialTable defaultState
        support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨hmeasurable, htail, _houtside⟩
  unfold decayingExplorationStochasticCommonCountBadEvent
  dsimp only
  unfold decayingExplorationStochasticCommonMeasure
  rw [(measurePreserving_eval_infinitePi
    (fun k => decayingExplorationStochasticWindowMeasure mdp initialState
      rewardSource initialTable defaultState baseVisitFloor k) n).measure_preimage
        hmeasurable.nullMeasurableSet]
  simpa [decayingExplorationStochasticWindowMeasure,
    decayingExplorationStochasticWindowSource] using htail

/-- Expected absolute scheduled stochastic realized-behavior regret. -/
noncomputable def decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) : Real :=
  integral
    (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
      initialTable defaultState baseVisitFloor)
    (fun omega =>
      |decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n omega|)

/--
Planner radius, count-failure contribution, and normalized stochastic MGF
first-moment contribution.
-/
noncomputable def decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound
    (mdp : MDP State Action) (baseVisitFloor : Real)
    (rewardVarianceProxy : NNReal) (n : Nat) : Real :=
  AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      mdp baseVisitFloor n +
    2 * (mdp.horizon : Real) *
      AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n +
    normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n)
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
      1 rewardVarianceProxy

/-- Expected absolute stochastic realized regret is nonnegative. -/
theorem decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    0 <= decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState baseVisitFloor n := by
  unfold decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret
  exact integral_nonneg fun _ => abs_nonneg _

/-- The explicit stochastic expected-absolute bound is nonnegative. -/
theorem decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound_nonneg
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor)
    (rewardVarianceProxy : NNReal) (n : Nat) :
    0 <= decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound
      mdp baseVisitFloor rewardVarianceProxy n := by
  unfold decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound
  exact add_nonneg
    (add_nonneg
      (by
        unfold AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
          AdaptiveEpisodeBatchSource.decayingExplorationAverageRecommendedExpectedRegretBound
          AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        apply add_nonneg
        · exact
            AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg
              mdp hhorizon
              (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
              (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
              (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
              (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
                mdp hbaseVisitFloor n)
        · unfold exploratoryBehaviorRegretCharge
          positivity)
      (mul_nonneg (by positivity)
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n).le))
    (normalizedSuccessorGlobalReturnMGFFirstMomentBound_nonneg
      mdp _ _ 1 rewardVarianceProxy)

/--
The common-space expected absolute stochastic realized regret is bounded by
the planner radius, one count-failure contribution, and the directly
integrated normalized sub-Gaussian deviation.
-/
theorem decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret_le_bound
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n <=
      decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound
        mdp baseVisitFloor rewardVarianceProxy n := by
  let mu := decayingExplorationStochasticCommonMeasure mdp initialState
    rewardSource initialTable defaultState baseVisitFloor
  let source := decayingExplorationStochasticWindowSource mdp initialState
    rewardSource initialTable defaultState baseVisitFloor n
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    mdp baseVisitFloor n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let planner :=
    AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      mdp baseVisitFloor n
  let envelope := 2 * (mdp.horizon : Real)
  let denom := (episodes : Real) * (rounds : Real)
  let process :=
    decayingExplorationStochasticRealizedBehaviorRegretProcess mdp initialState
      rewardSource initialTable defaultState baseVisitFloor n
  let deviation :=
    decayingExplorationStochasticCumulativeReturnDeviationProcess mdp
      initialState rewardSource initialTable defaultState baseVisitFloor n
  let bad := decayingExplorationStochasticCommonCountBadEvent mdp initialState
    initialTable defaultState baseVisitFloor n
  let overflow : DecayingExplorationStochasticWindowSpace mdp baseVisitFloor ->
      Real := bad.indicator (fun _ => envelope)
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes :=
    AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes_pos
      mdp baseVisitFloor n
  have hdenom : 0 < denom := by
    dsimp [denom]
    positivity
  have hplanner : 0 <= planner := by
    dsimp [planner]
    unfold AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      AdaptiveEpisodeBatchSource.decayingExplorationAverageRecommendedExpectedRegretBound
      AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    apply add_nonneg
    · exact
        AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg
          mdp hhorizon
          (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
          (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
          (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
          (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
            mdp hbaseVisitFloor n)
    · unfold exploratoryBehaviorRegretCharge
      positivity
  have henvelope : 0 <= envelope := by
    dsimp [envelope]
    positivity
  have hbad : MeasurableSet bad := by
    exact measurableSet_decayingExplorationStochasticCommonCountBadEvent
      mdp initialState rewardSource initialTable defaultState baseVisitFloor
        support hbaseFloor hrewardBound hhorizon hbaseVisitFloor n
  have hprocess : Integrable process mu := by
    exact integrable_decayingExplorationStochasticRealizedBehaviorRegretProcess
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound n
  have hmgf :=
    decayingExplorationStochasticCumulativeReturnDeviationProcess_hasSubgaussianMGF
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound n
  have hdeviation : Integrable deviation mu := by
    simpa [deviation, mu] using hmgf.integrable
  have hoverflow : Integrable overflow mu :=
    (integrable_const envelope).indicator hbad
  have hcount :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n rewardSource initialTable defaultState
        support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcount
  rcases hcount with ⟨_hcountMeasurable, _hcountTail, hcountOutside⟩
  have hpoint : forall omega,
      |process omega| <=
        planner + overflow omega + |deviation omega| / denom := by
    intro omega
    have hexpected :
        source.successorExpectedAverageRegret (omega n) rounds <=
          planner + overflow omega := by
      by_cases homega : omega ∈ bad
      · have hmean := source.successorExpectedAverageRegret_le_two_mul_horizon
          (omega n) rounds hrounds hrewardBound
        calc
          source.successorExpectedAverageRegret (omega n) rounds <=
              envelope := by simpa [envelope] using hmean
          _ <= planner + envelope := le_add_of_nonneg_left hplanner
          _ = planner + overflow omega := by
            simp [overflow, Set.indicator_of_mem homega]
      · have hnotCount : omega n ∉
            projectedAdaptiveCumulativeCountBadEvent
              (mdp := mdp) (initialState := initialState)
              (episodes := episodes) initialTable defaultState
              (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
                mdp rounds delta
                (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
                  mdp baseVisitFloor n))
              (AdaptiveEpisodeBatchSource.decayingExplorationRate n)
              (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
              rounds delta := by
          simpa [bad, decayingExplorationStochasticCommonCountBadEvent,
            rounds, episodes, delta] using homega
        have hgood := hcountOutside (omega n) hnotCount
        calc
          source.successorExpectedAverageRegret (omega n) rounds <=
              planner := by simpa [source, rounds, planner] using hgood.2
          _ = planner + overflow omega := by
            simp [overflow, Set.indicator_of_notMem homega]
    have habs :=
      source.abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
        (omega n) rounds hrounds hepisodes
        (planner + overflow omega) |deviation omega| hexpected le_rfl
    simpa [process, deviation, denom,
      decayingExplorationStochasticRealizedBehaviorRegretProcess,
      decayingExplorationStochasticCumulativeReturnDeviationProcess,
      source, rounds] using habs
  have hdom : Integrable
      (fun omega => planner + overflow omega + |deviation omega| / denom) mu :=
    ((integrable_const planner).add hoverflow).add
      (hdeviation.abs.div_const denom)
  have hoverflowIntegral : integral mu overflow = envelope * mu.real bad := by
    change integral mu (bad.indicator (fun _omega => envelope)) =
      envelope * mu.real bad
    rw [integral_indicator hbad, setIntegral_const]
    simp [Measure.real, smul_eq_mul, mul_comm]
  have htail := decayingExplorationStochasticCommonMeasure_countBadEvent_le
    mdp initialState baseVisitFloor rewardSource initialTable defaultState
      support hbaseFloor hrewardBound hhorizon hbaseVisitFloor n
  have htailReal : mu.real bad <= delta := by
    rw [Measure.real]
    have h := ENNReal.toReal_mono
      (by simp : ENNReal.ofReal delta ≠ ∞)
      (by simpa [mu, bad, delta] using htail)
    simpa [delta, ENNReal.toReal_ofReal
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n).le]
      using h
  have hdeviationIntegral :
      integral mu (fun omega => |deviation omega|) <=
        2 * Real.sqrt
          (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp rounds episodes 1 rewardVarianceProxy : Real) *
          Real.exp (1 / 2 : Real) := by
    simpa [deviation, mu, rounds, episodes] using
      (Concentration.integral_abs_le_two_mul_sqrt_mul_exp_half_of_hasSubgaussianMGF
        mu deviation
        (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
          mdp rounds episodes 1 rewardVarianceProxy)
        (by simpa [deviation, mu, rounds, episodes] using hmgf))
  change integral mu (fun omega => |process omega|) <=
    planner + envelope * delta +
      normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp episodes rounds
        1 rewardVarianceProxy
  calc
    integral mu (fun omega => |process omega|) <=
        integral mu
          (fun omega => planner + overflow omega + |deviation omega| / denom) :=
      integral_mono hprocess.abs hdom hpoint
    _ = planner + envelope * mu.real bad +
          integral mu (fun omega => |deviation omega|) / denom := by
      calc
        integral mu
            (fun omega => planner + overflow omega + |deviation omega| / denom) =
            integral mu (fun omega => planner + overflow omega) +
              integral mu (fun omega => |deviation omega| / denom) := by
          exact integral_add ((integrable_const planner).add hoverflow)
            (hdeviation.abs.div_const denom)
        _ = (integral mu (fun _omega => planner) + integral mu overflow) +
              integral mu (fun omega => |deviation omega|) / denom := by
          rw [integral_add (integrable_const planner) hoverflow, integral_div]
        _ = planner + envelope * mu.real bad +
              integral mu (fun omega => |deviation omega|) / denom := by
          rw [integral_const, hoverflowIntegral]
          simp [MeasureTheory.probReal_univ]
    _ <= planner + envelope * delta +
          (2 * Real.sqrt
            (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes 1 rewardVarianceProxy : Real) *
            Real.exp (1 / 2 : Real)) / denom := by
      exact add_le_add
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left htailReal henvelope))
        (div_le_div_of_nonneg_right hdeviationIntegral hdenom.le)
    _ = planner + envelope * delta +
          normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp episodes rounds
            1 rewardVarianceProxy := by
      rfl

/-- The explicit stochastic expected-absolute envelope tends to zero. -/
theorem decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor)
    (rewardVarianceProxy : NNReal) :
    Tendsto
      (decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound
        mdp baseVisitFloor rewardVarianceProxy) atTop (nhds 0) := by
  have hplanner :=
    AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor
  have hfailure : Tendsto
      (fun n => 2 * (mdp.horizon : Real) *
        AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _n : Nat => (2 * (mdp.horizon : Real))) atTop
        (nhds (2 * (mdp.horizon : Real))) := tendsto_const_nhds
    simpa using hconst.mul
      AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_tendsto_zero
  have hmgf :=
    decayingExplorationNormalizedSuccessorGlobalReturnMGFFirstMomentBound_tendsto_zero
      mdp baseVisitFloor 1 rewardVarianceProxy
  simpa [decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound]
    using (hplanner.add hfailure).add hmgf

/--
Terminal expected-consistency theorem for unbounded sampled rewards: every
coordinate is integrable, obeys the explicit three-term bound, and its expected
absolute realized regret tends to zero.
-/
theorem exploratorySource_decayingExplorationStochasticCommonMeasure_integrable_expectedAbsoluteRealizedBehaviorRegret_tendsto_zero
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
    (forall n,
      Integrable
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState baseVisitFloor n)
        (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor)) /\
      (forall n,
        decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret mdp
            initialState rewardSource initialTable defaultState baseVisitFloor n <=
          decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound
            mdp baseVisitFloor rewardVarianceProxy n) /\
      Tendsto
        (decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret mdp
          initialState rewardSource initialTable defaultState baseVisitFloor)
        atTop (nhds 0) := by
  refine ⟨fun n =>
    integrable_decayingExplorationStochasticRealizedBehaviorRegretProcess
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound n,
    fun n =>
      decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret_le_bound
        mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
          initialTable defaultState support hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor n,
    ?_⟩
  apply squeeze_zero
  · intro n
    exact decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret_nonneg
      mdp initialState rewardSource initialTable defaultState baseVisitFloor n
  · intro n
    exact decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret_le_bound
      mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor n
  · exact
      decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegretBound_tendsto_zero
        mdp hhorizon baseVisitFloor hbaseVisitFloor rewardVarianceProxy

/-- Every scheduled stochastic common-space coordinate belongs to `L1`. -/
theorem memLp_one_decayingExplorationStochasticRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    MemLp
      (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n)
      1
      (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor) := by
  rw [memLp_one_iff_integrable]
  exact integrable_decayingExplorationStochasticRealizedBehaviorRegretProcess
    mdp initialState rewardSource rewardVarianceProxy law initialTable
      defaultState baseVisitFloor hrewardBound n

/-- At exponent one, `eLpNorm` is the lifted expected absolute regret. -/
theorem eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    eLpNorm
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState baseVisitFloor n)
        1
        (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor) =
      ENNReal.ofReal
        (decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState baseVisitFloor n) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_decayingExplorationStochasticRealizedBehaviorRegretProcess
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound n)]
  simp [decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret,
    Real.norm_eq_abs]

/-- The exponent-one extended norm of the stochastic process tends to zero. -/
theorem eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_tendsto_zero
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
      (fun n => eLpNorm
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState baseVisitFloor n)
        1
        (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor))
      atTop (nhds 0) := by
  have hexpected :=
    (exploratorySource_decayingExplorationStochasticCommonMeasure_integrable_expectedAbsoluteRealizedBehaviorRegret_tendsto_zero
      mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor).2.2
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hexpected
  simpa only [ENNReal.ofReal_zero,
    eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_eq
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound] using hofReal

/-- Canonical `L1` norm-of-the-difference convergence. -/
theorem eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
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
      (fun n => eLpNorm
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
            initialState rewardSource initialTable defaultState baseVisitFloor n -
          (fun _ => 0))
        1
        (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor))
      atTop (nhds 0) := by
  have h :=
    eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_tendsto_zero
      mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  convert h using 1
  funext n
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun omega => by simp

/-- The stochastic scheduled realized-regret process as an `Lp Real 1` value. -/
noncomputable def decayingExplorationStochasticRealizedBehaviorRegretLp
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    Lp Real 1
      (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor) :=
  (memLp_one_decayingExplorationStochasticRealizedBehaviorRegretProcess
    mdp initialState rewardSource rewardVarianceProxy law initialTable
      defaultState baseVisitFloor hrewardBound n).toLp
    (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState baseVisitFloor n)

/-- The named stochastic `Lp` coordinate represents the original process a.e. -/
theorem decayingExplorationStochasticRealizedBehaviorRegretLp_coeFn_ae_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    (decayingExplorationStochasticRealizedBehaviorRegretLp mdp initialState
        rewardSource rewardVarianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound n :
      DecayingExplorationStochasticWindowSpace mdp baseVisitFloor -> Real) =ᵐ[
        decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor]
      decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n := by
  exact (memLp_one_decayingExplorationStochasticRealizedBehaviorRegretProcess
    mdp initialState rewardSource rewardVarianceProxy law initialTable
      defaultState baseVisitFloor hrewardBound n).coeFn_toLp

/-- The named stochastic `Lp Real 1` process converges to zero. -/
theorem decayingExplorationStochasticRealizedBehaviorRegretLp_tendsto_zero
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
      (decayingExplorationStochasticRealizedBehaviorRegretLp mdp initialState
        rewardSource rewardVarianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound)
      atTop (nhds 0) := by
  let mu := decayingExplorationStochasticCommonMeasure mdp initialState
    rewardSource initialTable defaultState baseVisitFloor
  let process := fun n =>
    decayingExplorationStochasticRealizedBehaviorRegretProcess mdp initialState
      rewardSource initialTable defaultState baseVisitFloor n
  have hmem : forall n, MemLp (process n) 1 mu := fun n =>
    memLp_one_decayingExplorationStochasticRealizedBehaviorRegretProcess
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound n
  have hzero : MemLp (fun _ : DecayingExplorationStochasticWindowSpace mdp
      baseVisitFloor => (0 : Real)) 1 mu := MemLp.zero'
  have hnorm :=
    eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
      mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hLp :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' process hmem (fun _ => (0 : Real))
      hzero).2 (by simpa [process, mu] using hnorm)
  simpa [decayingExplorationStochasticRealizedBehaviorRegretLp, process, mu]
    using hLp

/--
Terminal stochastic `L1` theorem: coordinate membership, exact exponent-one
norms, `Lp` convergence, and induced convergence in measure hold on the same
independent product of complete scheduled experiments.
-/
theorem exploratorySource_decayingExplorationStochasticCommonMeasure_memLp_eLpNorm_L1_tendsto_zero
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
    (forall n, MemLp
      (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n)
      1
      (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor)) /\
    (forall n, eLpNorm
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState baseVisitFloor n)
        1
        (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor) =
      ENNReal.ofReal
        (decayingExplorationStochasticExpectedAbsoluteRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState baseVisitFloor n)) /\
    Tendsto
      (fun n => eLpNorm
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
            initialState rewardSource initialTable defaultState baseVisitFloor n -
          (fun _ => 0))
        1
        (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor))
      atTop (nhds 0) /\
    Tendsto
      (decayingExplorationStochasticRealizedBehaviorRegretLp mdp initialState
        rewardSource rewardVarianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound)
      atTop (nhds 0) /\
    TendstoInMeasure
      (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor)
      (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor)
      atTop (fun _ => 0) := by
  have hmem := fun n =>
    memLp_one_decayingExplorationStochasticRealizedBehaviorRegretProcess
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound n
  have hnorm :=
    eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
      mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  refine ⟨hmem, fun n =>
    eLpNorm_one_decayingExplorationStochasticRealizedBehaviorRegretProcess_eq
      mdp initialState rewardSource rewardVarianceProxy law initialTable
        defaultState baseVisitFloor hrewardBound n,
    hnorm,
    decayingExplorationStochasticRealizedBehaviorRegretLp_tendsto_zero
      mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    ?_⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n => (hmem n).aestronglyMeasurable)
    (by fun_prop) hnorm

end AdaptiveCumulativeStochasticEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
