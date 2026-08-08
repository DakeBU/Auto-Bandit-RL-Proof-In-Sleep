import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticRealizedBehaviorRegret
import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeDecayingExplorationBehaviorConsistency

/-!
# Stochastic cumulative decaying-exploration realized consistency

This module lifts the cumulative empirical-optimistic exploratory source to
complete stochastic-reward episode batches. Policy selection reads only the
known-reward projection of the sampled prefix. The first layer proves the exact
complete trajectory pushforward to the deterministic cumulative source; later
layers consume the deterministic decaying-exploration count certificate and
the globally centered stochastic return tail.

Every schedule index still uses its own finite batch and infinite trajectory
space. No common-process, almost-sure, anytime, or reward-mean-estimation claim
is made here.
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

namespace MDP

/-- One-episode proxy underlying the globally centered stochastic batch proxy. -/
noncomputable def globalReturnDeviationPerEpisodeVarianceProxy
    (mdp : MDP State Action) (rewardBound rewardVarianceProxy : NNReal) : NNReal :=
  (((mdp.horizon : NNReal) * rewardVarianceProxy +
      meanBellmanInnovationVarianceProxy rewardBound mdp.horizon).sqrt +
    (mdp.initialPolicyValueVarianceProxy rewardBound).sqrt) ^ 2

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The honest global iid proxy is exactly episode-linear. -/
theorem iidGlobalSampledCumulativeReturnDeviationVarianceProxy_eq
    (mdp : MDP State Action) (episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) :
    mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy episodes
        rewardBound rewardVarianceProxy =
      (episodes : NNReal) *
        mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy := by
  unfold iidGlobalSampledCumulativeReturnDeviationVarianceProxy
    iidSampledCumulativeReturnDeviationVarianceProxy
    iidInitialPolicyValueDeviationVarianceProxy
    globalReturnDeviationPerEpisodeVarianceProxy
  rw [NNReal.sqrt_mul, NNReal.sqrt_mul]
  ring_nf
  simp
  ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Positive horizon and positive reward bound make the per-episode proxy positive. -/
theorem globalReturnDeviationPerEpisodeVarianceProxy_pos
    (mdp : MDP State Action) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : 0 < rewardBound) (hhorizon : 0 < mdp.horizon) :
    0 < mdp.globalReturnDeviationPerEpisodeVarianceProxy
      rewardBound rewardVarianceProxy := by
  have hmean : 0 < meanBellmanInnovationVarianceProxy
      rewardBound mdp.horizon :=
    meanBellmanInnovationVarianceProxy_pos hrewardBound hhorizon
  have hinside : 0 < (mdp.horizon : NNReal) * rewardVarianceProxy +
      meanBellmanInnovationVarianceProxy rewardBound mdp.horizon :=
    lt_of_lt_of_le hmean (le_add_of_nonneg_left (by positivity))
  unfold globalReturnDeviationPerEpisodeVarianceProxy
  positivity

end MDP

namespace AdaptiveStochasticEpisodeBatchSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The successor proxy is exactly rounds times episodes times one base proxy. -/
theorem cumulativeSuccessorGlobalReturnVarianceProxy_coe
    (mdp : MDP State Action) (rounds episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) :
    ((cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy : NNReal) : Real) =
      (rounds : Real) * (episodes : Real) *
        (mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy : Real) := by
  rw [cumulativeSuccessorGlobalReturnVarianceProxy_eq]
  rw [mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy_eq]
  push_cast
  ring

/-- Globally centered stochastic return radius normalized by all successor samples. -/
noncomputable def normalizedSuccessorGlobalReturnConfidenceRadius
    (mdp : MDP State Action) (episodes rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (delta : Real) : Real :=
  Concentration.subGaussianSumConfidenceRadius
      (cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy) delta /
    ((episodes : Real) * (rounds : Real))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem normalizedSuccessorGlobalReturnConfidenceRadius_nonneg
    (mdp : MDP State Action) (episodes rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (delta : Real) :
    0 <= normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
      rewardBound rewardVarianceProxy delta := by
  unfold normalizedSuccessorGlobalReturnConfidenceRadius
  exact div_nonneg
    (Concentration.subGaussianSumConfidenceRadius_nonneg _ _)
    (mul_nonneg (by positivity) (by positivity))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Exact normalized-radius formula after exposing episode and round scaling. -/
theorem normalizedSuccessorGlobalReturnConfidenceRadius_eq
    (mdp : MDP State Action) (episodes rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (delta : Real)
    (hepisodes : 0 < episodes) (hrounds : 0 < rounds)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
        rewardBound rewardVarianceProxy delta =
      Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          ((episodes : Real) * (rounds : Real))) := by
  have hepisodesReal : 0 < (episodes : Real) := by exact_mod_cast hepisodes
  have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
  have hlog : 0 <= Real.log (2 / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    linarith
  have hradiusSq :=
    Concentration.subGaussianSumConfidenceRadius_sq
      (cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy) delta hdelta hdelta_le_one
  rw [cumulativeSuccessorGlobalReturnVarianceProxy_coe] at hradiusSq
  have hsqrtSq :
      (Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          ((episodes : Real) * (rounds : Real)))) ^ 2 =
        2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          ((episodes : Real) * (rounds : Real)) := by
    rw [Real.sq_sqrt]
    positivity
  have hlhsNonneg :
      0 <= normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
        rewardBound rewardVarianceProxy delta :=
    normalizedSuccessorGlobalReturnConfidenceRadius_nonneg _ _ _ _ _ _
  have hrhsNonneg :
      0 <= Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          ((episodes : Real) * (rounds : Real))) := Real.sqrt_nonneg _
  have hsq :
      (normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
        rewardBound rewardVarianceProxy delta) ^ 2 =
      (Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          ((episodes : Real) * (rounds : Real)))) ^ 2 := by
    unfold normalizedSuccessorGlobalReturnConfidenceRadius
    rw [div_pow, hradiusSq, hsqrtSq]
    field_simp [ne_of_gt hepisodesReal, ne_of_gt hroundsReal]
  nlinarith

/-- A simple inverse-scale envelope for the scheduled stochastic radius. -/
noncomputable def decayingExplorationStochasticReturnRadiusEnvelope
    (mdp : MDP State Action) (rewardBound rewardVarianceProxy : NNReal)
    (n : Nat) : Real :=
  Real.sqrt
      (4 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
        rewardBound rewardVarianceProxy : Real)) /
    (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem normalizedSuccessorGlobalReturnConfidenceRadius_le_decayingEnvelope
    (mdp : MDP State Action) (episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (n : Nat)
    (hepisodes : 0 < episodes) :
    normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        rewardBound rewardVarianceProxy
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) <=
      decayingExplorationStochasticReturnRadiusEnvelope mdp
        rewardBound rewardVarianceProxy n := by
  have hrounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  rw [normalizedSuccessorGlobalReturnConfidenceRadius_eq mdp episodes
    (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
    rewardBound rewardVarianceProxy
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
    hepisodes hrounds
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)]
  unfold decayingExplorationStochasticReturnRadiusEnvelope
  let scale : Real :=
    (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real)
  let base : Real :=
    (mdp.globalReturnDeviationPerEpisodeVarianceProxy
      rewardBound rewardVarianceProxy : Real)
  have hscalePos : 0 < scale := by
    dsimp [scale]
    exact_mod_cast AdaptiveEpisodeBatchSource.decayingExplorationScale_pos n
  have hscaleOne : 1 <= scale := by
    dsimp [scale]
    exact_mod_cast (show 1 <=
      AdaptiveEpisodeBatchSource.decayingExplorationScale n by
        simp [AdaptiveEpisodeBatchSource.decayingExplorationScale])
  have hepisodesReal : 1 <= (episodes : Real) := by exact_mod_cast hepisodes
  have hbase : 0 <= base := by positivity
  have hdeltaRewrite :
      2 / AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n =
        2 * scale := by
    simp [scale, AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta,
      AdaptiveEpisodeBatchSource.decayingExplorationScale]
  have hroundsCast :
      ((AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n : Nat) : Real) =
        scale ^ (mdp.horizon + 4) := by
    simp [AdaptiveEpisodeBatchSource.decayingExplorationRounds, scale]
  rw [hdeltaRewrite, hroundsCast]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [div_pow, Real.sq_sqrt (by positivity : 0 <= 4 * base)]
    have hlogUpper : Real.log (2 * scale) <= 2 * scale := by
      exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have hpow : scale <= scale ^ (mdp.horizon + 2) := by
      simpa using pow_le_pow_right₀ hscaleOne
        (show 1 <= mdp.horizon + 2 by omega)
    have hnum :
        2 * base * Real.log (2 * scale) <=
          4 * base * (episodes : Real) * scale ^ (mdp.horizon + 2) := by
      calc
        2 * base * Real.log (2 * scale) <=
            2 * base * (2 * scale) :=
          mul_le_mul_of_nonneg_left hlogUpper (by positivity)
        _ = 4 * base * scale := by ring
        _ <= 4 * base * scale ^ (mdp.horizon + 2) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ <= 4 * base * (episodes : Real) *
            scale ^ (mdp.horizon + 2) := by
          calc
            4 * base * scale ^ (mdp.horizon + 2) =
                (4 * base * scale ^ (mdp.horizon + 2)) * 1 := by ring
            _ <= (4 * base * scale ^ (mdp.horizon + 2)) *
                (episodes : Real) :=
              mul_le_mul_of_nonneg_left hepisodesReal (by positivity)
            _ = 4 * base * (episodes : Real) *
                scale ^ (mdp.horizon + 2) := by ring
    apply (div_le_iff₀
      (mul_pos (by positivity : 0 < (episodes : Real))
        (pow_pos hscalePos _))).2
    calc
      2 * base * Real.log (2 * scale) <=
          4 * base * (episodes : Real) * scale ^ (mdp.horizon + 2) := hnum
      _ = (4 * base / scale ^ 2) *
          ((episodes : Real) * scale ^ (mdp.horizon + 4)) := by
        rw [show mdp.horizon + 4 = (mdp.horizon + 2) + 2 by omega,
          pow_add]
        field_simp [ne_of_gt hscalePos]
        ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationStochasticReturnRadiusEnvelope_tendsto_zero
    (mdp : MDP State Action) (rewardBound rewardVarianceProxy : NNReal) :
    Tendsto
      (decayingExplorationStochasticReturnRadiusEnvelope mdp
        rewardBound rewardVarianceProxy) atTop (nhds 0) := by
  have hscale : Tendsto
      (fun n : Nat =>
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real))
      atTop atTop := by
    change Tendsto (fun n : Nat => (((n + 2 : Nat) : Real))) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  unfold decayingExplorationStochasticReturnRadiusEnvelope
  exact (tendsto_const_nhds.div_atTop hscale :
      Tendsto
        (fun n : Nat =>
          Real.sqrt
              (4 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
                rewardBound rewardVarianceProxy : Real)) /
            (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real))
        atTop (nhds 0))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact scheduled stochastic return radius tends to zero. -/
theorem decayingExplorationNormalizedSuccessorGlobalReturnRadius_tendsto_zero
    (mdp : MDP State Action) (baseVisitFloor : Real)
    (rewardBound rewardVarianceProxy : NNReal) :
    Tendsto
      (fun n =>
        normalizedSuccessorGlobalReturnConfidenceRadius mdp
          (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
            mdp baseVisitFloor n)
          (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
          rewardBound rewardVarianceProxy
          (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact normalizedSuccessorGlobalReturnConfidenceRadius_nonneg _ _ _ _ _ _
  · intro n
    exact normalizedSuccessorGlobalReturnConfidenceRadius_le_decayingEnvelope
      mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n)
      rewardBound rewardVarianceProxy n
      (by
        unfold AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        exact
          AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes_pos
            _ _ _ _)
  · exact decayingExplorationStochasticReturnRadiusEnvelope_tendsto_zero
      mdp rewardBound rewardVarianceProxy

/-- Stochastic realized-behavior certificate at schedule index `n`. -/
noncomputable def decayingExplorationStochasticAverageRealizedBehaviorRegretBound
    (mdp : MDP State Action) (baseVisitFloor : Real)
    (rewardVarianceProxy : NNReal) (n : Nat) : Real :=
  AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      mdp baseVisitFloor n +
    normalizedSuccessorGlobalReturnConfidenceRadius mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n)
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
      1 rewardVarianceProxy
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)

/-- Projected-count and stochastic-return deviations consume one share each. -/
noncomputable def decayingExplorationStochasticRealizedFailureBudget
    (n : Nat) : ENNReal :=
  ENNReal.ofReal (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) +
    ENNReal.ofReal (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)

theorem decayingExplorationStochasticAverageRealizedBehaviorRegretBound_nonneg
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor)
    (rewardVarianceProxy : NNReal) (n : Nat) :
    0 <= decayingExplorationStochasticAverageRealizedBehaviorRegretBound
      mdp baseVisitFloor rewardVarianceProxy n := by
  unfold decayingExplorationStochasticAverageRealizedBehaviorRegretBound
  exact add_nonneg
    (by
      unfold AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        AdaptiveEpisodeBatchSource.decayingExplorationAverageRecommendedExpectedRegretBound
        AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
      exact add_nonneg
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg
          mdp hhorizon
          (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
          (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
          (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
          (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos mdp
            hbaseVisitFloor n))
        (by unfold exploratoryBehaviorRegretCharge; positivity))
    (normalizedSuccessorGlobalReturnConfidenceRadius_nonneg _ _ _ _ _ _)

theorem decayingExplorationStochasticAverageRealizedBehaviorRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor)
    (rewardVarianceProxy : NNReal) :
    Tendsto
      (decayingExplorationStochasticAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor rewardVarianceProxy) atTop (nhds 0) := by
  simpa [decayingExplorationStochasticAverageRealizedBehaviorRegretBound] using
    (AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor).add
      (decayingExplorationNormalizedSuccessorGlobalReturnRadius_tendsto_zero
        mdp baseVisitFloor 1 rewardVarianceProxy)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationStochasticRealizedFailureBudget_tendsto_zero :
    Tendsto decayingExplorationStochasticRealizedFailureBudget
      atTop (nhds 0) := by
  simpa [decayingExplorationStochasticRealizedFailureBudget] using
    AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_ennreal_tendsto_zero.add
      AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_ennreal_tendsto_zero

theorem decayingExplorationStochasticRealizedFailureAndRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor)
    (rewardVarianceProxy : NNReal) :
    Tendsto
      (fun n =>
        (decayingExplorationStochasticRealizedFailureBudget n,
          decayingExplorationStochasticAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor rewardVarianceProxy n))
      atTop (nhds (0, 0)) := by
  rw [nhds_prod_eq]
  exact decayingExplorationStochasticRealizedFailureBudget_tendsto_zero.prodMk
    (decayingExplorationStochasticAverageRealizedBehaviorRegretBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor rewardVarianceProxy)

end AdaptiveStochasticEpisodeBatchSource

namespace AdaptiveCumulativeStochasticEmpiricalOptimisticSource

/--
Stochastic-reward lift of the cumulative empirical-optimistic exploratory
source. The cumulative table selector is evaluated only on projected history.
-/
noncomputable def exploratorySource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    AdaptiveStochasticEpisodeBatchSource mdp initialState episodes where
  rewardSource := rewardSource
  initialPolicy :=
    initialTable.exploratoryPolicy explorationRate hexplorationRate
  successorPolicy n history :=
    (AdaptiveCumulativeEmpiricalOptimisticSource.successorTable defaultState
      countRadius n
      (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
        (mdp := mdp) episodes n history)).exploratoryPolicy
          explorationRate hexplorationRate
  batchKernel n :=
    (DeterministicMarkovPolicyTable.exploratoryIIDStochasticEpisodeBatchKernel
      rewardSource initialState episodes explorationRate hexplorationRate).comap
        (fun history =>
          AdaptiveCumulativeEmpiricalOptimisticSource.successorTable defaultState
            countRadius n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history))
        ((AdaptiveCumulativeEmpiricalOptimisticSource.measurable_successorTable
          defaultState countRadius n).comp
            (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n))
  batchKernel_isMarkov n := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      ((AdaptiveCumulativeEmpiricalOptimisticSource.measurable_successorTable
        defaultState countRadius n).comp
          (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n))
  batchKernel_eq_iidStochasticTrajectoryFamilyMeasure n history := by
    rw [ProbabilityTheory.Kernel.comap_apply]
    rfl
  measurable_successorSampledReturnDeviation n := by
    exact
      AdaptiveStochasticEmpiricalOptimisticSource.measurable_selectedExploratorySampledReturnDeviation
        (fun history =>
          AdaptiveCumulativeEmpiricalOptimisticSource.successorTable defaultState
            countRadius n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history))
        ((AdaptiveCumulativeEmpiricalOptimisticSource.measurable_successorTable
          defaultState countRadius n).comp
            (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n))
        explorationRate hexplorationRate

omit [Nonempty State] in
/-- The initial policies of the stochastic lift and deterministic source agree. -/
theorem exploratorySource_initialPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState countRadius explorationRate hexplorationRate).initialPolicy =
      (AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
        initialState episodes initialTable defaultState countRadius
          explorationRate hexplorationRate).initialPolicy := by
  rfl

omit [Nonempty State] in
/-- Every stochastic successor policy is the deterministic projected policy. -/
theorem exploratorySource_successorPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState countRadius explorationRate hexplorationRate).successorPolicy
        n history =
      (AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
        initialState episodes initialTable defaultState countRadius
          explorationRate hexplorationRate).successorPolicy n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history) := by
  rfl

omit [Nonempty State] in
/-- The initial stochastic batch maps to the deterministic cumulative fiber. -/
theorem exploratorySource_initialBatch_map_knownRewardEpisodeBatch
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    (rewardSource.iidStochasticTrajectoryFamilyMeasure
      (exploratorySource mdp initialState episodes rewardSource initialTable
        defaultState countRadius explorationRate
          hexplorationRate).initialPolicy initialState episodes).map
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
          (mdp := mdp) episodes) =
      (AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
        initialState episodes initialTable defaultState countRadius
          explorationRate hexplorationRate).initialPolicy.iidEpisodeBatchMeasure
            initialState episodes := by
  rw [exploratorySource_initialPolicy rewardSource initialTable defaultState
    countRadius explorationRate hexplorationRate]
  exact
    rewardSource.iidStochasticTrajectoryFamilyMeasure_map_knownRewardEpisodeBatch_eq_iidEpisodeBatchMeasure
      _ initialState episodes

omit [Nonempty State] in
/-- Every selected stochastic successor batch maps to its deterministic fiber. -/
theorem exploratorySource_batchKernel_map_knownRewardEpisodeBatch
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    ((exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState countRadius explorationRate hexplorationRate).batchKernel
        n history).map
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
            (mdp := mdp) episodes) =
      (AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
        initialState episodes initialTable defaultState countRadius
          explorationRate hexplorationRate).batchKernel n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history) := by
  let stochasticSource := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState countRadius explorationRate hexplorationRate
  let deterministicSource :=
    AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
      initialState episodes initialTable defaultState countRadius
        explorationRate hexplorationRate
  rw [stochasticSource.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure]
  rw [deterministicSource.batchKernel_eq_iidEpisodeBatchMeasure]
  have hpolicy :
      stochasticSource.successorPolicy n history =
        deterministicSource.successorPolicy n
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n history) :=
    exploratorySource_successorPolicy rewardSource initialTable defaultState
      countRadius explorationRate hexplorationRate n history
  rw [hpolicy]
  exact
    rewardSource.iidStochasticTrajectoryFamilyMeasure_map_knownRewardEpisodeBatch_eq_iidEpisodeBatchMeasure
      _ initialState episodes

omit [Nonempty State] in
/-- Projected prefix and next-batch joint law of the cumulative source. -/
theorem exploratorySource_trajectoryMeasure_map_projectedPrefix_next_eq_compProd
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) :
    let stochasticSource := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState countRadius explorationRate hexplorationRate
    let deterministicSource :=
      AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
        initialState episodes initialTable defaultState countRadius
          explorationRate hexplorationRate
    stochasticSource.trajectoryMeasure.map
        (fun trajectory =>
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory),
            MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
              (mdp := mdp) episodes (trajectory (n + 1)))) =
      stochasticSource.trajectoryMeasure.map
          (fun trajectory =>
            MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory)) ⊗ₘ
        deterministicSource.batchKernel n := by
  dsimp only
  let stochasticSource := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState countRadius explorationRate hexplorationRate
  let deterministicSource :=
    AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
      initialState episodes initialTable defaultState countRadius
        explorationRate hexplorationRate
  let prefixProjection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
      (mdp := mdp) episodes n
  let batchProjection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
      (mdp := mdp) episodes
  let projectedPrefix :=
    fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
      prefixProjection (Preorder.frestrictLe n trajectory)
  let projectedPair :=
    fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
      (projectedPrefix trajectory, batchProjection (trajectory (n + 1)))
  let originalPair :=
    fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
      (Preorder.frestrictLe n trajectory, trajectory (n + 1))
  have hprefixProjection : Measurable prefixProjection :=
    MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
      (mdp := mdp) episodes n
  have hbatchProjection : Measurable batchProjection :=
    MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
      (mdp := mdp) episodes
  have hrestrict : Measurable
      (Preorder.frestrictLe n : StochasticEpisodeBatchTrajectory mdp episodes ->
        StochasticEpisodeBatchPrefix mdp episodes n) :=
    Preorder.measurable_frestrictLe n
  have hprojectedPrefix : Measurable projectedPrefix :=
    hprefixProjection.comp hrestrict
  have horiginalPair : Measurable originalPair :=
    hrestrict.prodMk (measurable_pi_apply (n + 1))
  have hprodMap : Measurable (Prod.map prefixProjection batchProjection) :=
    hprefixProjection.prodMap hbatchProjection
  have hbaseMap :
      (stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)).map
          prefixProjection =
        stochasticSource.trajectoryMeasure.map projectedPrefix := by
    rw [Measure.map_map hprefixProjection hrestrict]
    rfl
  letI : IsProbabilityMeasure
      (stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)) :=
    Measure.isProbabilityMeasure_map hrestrict.aemeasurable
  letI : IsProbabilityMeasure
      (stochasticSource.trajectoryMeasure.map projectedPrefix) :=
    Measure.isProbabilityMeasure_map hprojectedPrefix.aemeasurable
  have hcompProdMap :
      ((stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)) ⊗ₘ
          stochasticSource.batchKernel n).map
            (Prod.map prefixProjection batchProjection) =
        stochasticSource.trajectoryMeasure.map projectedPrefix ⊗ₘ
          deterministicSource.batchKernel n := by
    exact ProbabilityTheory.measure_compProd_map_prodMap_of_map_eq
      (stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n))
      (stochasticSource.batchKernel n)
      (stochasticSource.trajectoryMeasure.map projectedPrefix)
      (deterministicSource.batchKernel n)
      prefixProjection hprefixProjection batchProjection hbatchProjection
      hbaseMap
      (fun history =>
        exploratorySource_batchKernel_map_knownRewardEpisodeBatch rewardSource
          initialTable defaultState countRadius explorationRate
            hexplorationRate n history)
  change stochasticSource.trajectoryMeasure.map projectedPair =
    stochasticSource.trajectoryMeasure.map projectedPrefix ⊗ₘ
      deterministicSource.batchKernel n
  calc
    stochasticSource.trajectoryMeasure.map projectedPair =
        (stochasticSource.trajectoryMeasure.map originalPair).map
          (Prod.map prefixProjection batchProjection) := by
      rw [Measure.map_map hprodMap horiginalPair]
      rfl
    _ = ((stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)) ⊗ₘ
          stochasticSource.batchKernel n).map
            (Prod.map prefixProjection batchProjection) := by
      rw [stochasticSource.trajectoryMeasure_prefix_compProd n]
    _ = stochasticSource.trajectoryMeasure.map projectedPrefix ⊗ₘ
          deterministicSource.batchKernel n := hcompProdMap

omit [Nonempty State] in
/-- Conditional projected next-batch law for the cumulative source. -/
theorem exploratorySource_trajectoryMeasure_condDistrib_projectedNext
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [Nonempty (EpisodeBatch mdp episodes)]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) :
    let stochasticSource := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState countRadius explorationRate hexplorationRate
    let deterministicSource :=
      AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
        initialState episodes initialTable defaultState countRadius
          explorationRate hexplorationRate
    ProbabilityTheory.condDistrib
        (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
          MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
            (mdp := mdp) episodes (trajectory (n + 1)))
        (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
          MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory))
        stochasticSource.trajectoryMeasure =ᵐ[
          stochasticSource.trajectoryMeasure.map
            (fun trajectory =>
              MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
                (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory))]
      deterministicSource.batchKernel n := by
  dsimp only
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
  · exact
      (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
        (mdp := mdp) episodes n).comp (Preorder.measurable_frestrictLe n)
  · exact
      (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
        (mdp := mdp) episodes).comp (measurable_pi_apply (n + 1))
  · exact
      exploratorySource_trajectoryMeasure_map_projectedPrefix_next_eq_compProd
        rewardSource initialTable defaultState countRadius explorationRate
          hexplorationRate n

omit [Nonempty State] in
/-- The complete known-reward projection equals the deterministic source law. -/
theorem exploratorySource_trajectoryMeasure_map_knownRewardEpisodeBatchTrajectory
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [Nonempty (EpisodeBatch mdp episodes)]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    let stochasticSource := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState countRadius explorationRate hexplorationRate
    let deterministicSource :=
      AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
        initialState episodes initialTable defaultState countRadius
          explorationRate hexplorationRate
    stochasticSource.trajectoryMeasure.map
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
          (mdp := mdp) episodes) =
      deterministicSource.trajectoryMeasure := by
  dsimp only
  let stochasticSource := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState countRadius explorationRate hexplorationRate
  let deterministicSource :=
    AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
      initialState episodes initialTable defaultState countRadius
        explorationRate hexplorationRate
  let projection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes
  have hzero :
      stochasticSource.trajectoryMeasure.map
          (fun trajectory => projection trajectory 0) =
        deterministicSource.initialPolicy.iidEpisodeBatchMeasure
          initialState episodes := by
    let batchProjection :=
      MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
        (mdp := mdp) episodes
    have hbatchProjection : Measurable batchProjection :=
      MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
        (mdp := mdp) episodes
    calc
      stochasticSource.trajectoryMeasure.map
          (fun trajectory => projection trajectory 0) =
        (stochasticSource.trajectoryMeasure.map (Function.eval 0)).map
          batchProjection := by
          rw [Measure.map_map hbatchProjection (measurable_pi_apply 0)]
          rfl
      _ = (stochasticSource.rewardSource.iidStochasticTrajectoryFamilyMeasure
          stochasticSource.initialPolicy initialState episodes).map
            batchProjection := by
          rw [stochasticSource.trajectoryMeasure_map_eval_zero]
      _ = deterministicSource.initialPolicy.iidEpisodeBatchMeasure
          initialState episodes := by
        have hrewards : stochasticSource.rewardSource = rewardSource := by
          rfl
        rw [hrewards]
        exact exploratorySource_initialBatch_map_knownRewardEpisodeBatch rewardSource
          initialTable defaultState countRadius explorationRate
            hexplorationRate
  have hcond : forall n,
      ProbabilityTheory.condDistrib
          (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
            projection trajectory (n + 1))
          (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
            History.finiteRewardHistoryOfTrace (projection trajectory) n)
          stochasticSource.trajectoryMeasure =ᵐ[
            stochasticSource.trajectoryMeasure.map
              (fun trajectory =>
                History.finiteRewardHistoryOfTrace (projection trajectory) n)]
        deterministicSource.batchKernel n := by
    intro n
    simpa [projection, History.finiteRewardHistoryOfTrace] using
      (exploratorySource_trajectoryMeasure_condDistrib_projectedNext
        rewardSource initialTable defaultState countRadius explorationRate
          hexplorationRate n)
  simpa [stochasticSource, deterministicSource, projection,
    AdaptiveEpisodeBatchSource.trajectoryMeasure] using
    (RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib
      (mu := stochasticSource.trajectoryMeasure)
      (mu0 := deterministicSource.initialPolicy.iidEpisodeBatchMeasure
        initialState episodes)
      (reward := projection)
      (hreward := fun round =>
        (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
          (mdp := mdp) episodes).comp (measurable_pi_apply round))
      (kernel := deterministicSource.batchKernel)
      hzero hcond)

/-- Pullback of the deterministic cumulative count event. -/
def projectedAdaptiveCumulativeCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (delta : Real) :
    Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
  MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes ⁻¹'
    (AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
      initialState episodes initialTable defaultState countRadius
        explorationRate hexplorationRate).adaptiveCumulativeCountBadEvent
          rounds delta

/-- The cumulative finite-table selector supplies global-return measurability. -/
noncomputable instance instExploratorySourceGlobalReturnMeasurability
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState countRadius explorationRate
        hexplorationRate).GlobalReturnMeasurability where
  measurable_successorGlobalReturnDeviation n := by
    exact
      AdaptiveStochasticEmpiricalOptimisticSource.measurable_selectedExploratoryGlobalReturnDeviation
        (fun history =>
          AdaptiveCumulativeEmpiricalOptimisticSource.successorTable defaultState
            countRadius n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history))
        ((AdaptiveCumulativeEmpiricalOptimisticSource.measurable_successorTable
          defaultState countRadius n).comp
            (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n))
        explorationRate hexplorationRate

omit [Nonempty State] in
/-- Stochastic successor expected regret is the projected cumulative quantity. -/
theorem exploratorySource_successorExpectedCumulativeRegret_eq_projected
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState countRadius explorationRate
        hexplorationRate).successorExpectedCumulativeRegret trajectory rounds =
      adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
        (initialState := initialState)
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
          (mdp := mdp) episodes trajectory)
        defaultState countRadius explorationRate hexplorationRate rounds := by
  unfold AdaptiveStochasticEpisodeBatchSource.successorExpectedCumulativeRegret
    adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
  apply Finset.sum_congr rfl
  intro round _hround
  unfold AdaptiveStochasticEpisodeBatchSource.successorPolicyAt
  rw [exploratorySource_successorPolicy]
  rw [MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix_frestrictLe]
  rfl

omit [Nonempty State] in
/-- Average stochastic successor expected regret is the projected average. -/
theorem exploratorySource_successorExpectedAverageRegret_eq_projected
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState countRadius explorationRate
        hexplorationRate).successorExpectedAverageRegret trajectory rounds =
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
        (initialState := initialState)
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
          (mdp := mdp) episodes trajectory)
        defaultState countRadius explorationRate hexplorationRate rounds := by
  unfold AdaptiveStochasticEpisodeBatchSource.successorExpectedAverageRegret
    adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
  rw [exploratorySource_successorExpectedCumulativeRegret_eq_projected]

/--
The projected stochastic source inherits the deterministic decaying count,
optimism, and expected exploratory-behavior certificate for one window.
-/
theorem exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real) (n : Nat)
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [Nonempty
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
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
    MeasurableSet countBadEvent /\
      source.trajectoryMeasure countBadEvent <= ENNReal.ofReal delta /\
      forall trajectory, trajectory ∉ countBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              (projection trajectory) defaultState countRadius round
              ).upperValueRemaining mdp.horizon le_rfl state) /\
        source.successorExpectedAverageRegret trajectory rounds <=
          AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
            mdp baseVisitFloor n := by
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
  let deterministicSource :=
    AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource mdp
      initialState episodes initialTable defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  let projection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes
  let deterministicBad := deterministicSource.adaptiveCumulativeCountBadEvent
    rounds delta
  let countBadEvent := projection ⁻¹' deterministicBad
  have hparent :=
    AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n initialTable defaultState support
        hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hparent
  rcases hparent with
    ⟨hdeterministicMeasurable, hdeterministicTail, _hviolationSubset,
      _hviolationTail, hdeterministicGood⟩
  have hprojection : Measurable projection :=
    MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes
  have htrajectoryMap :
      source.trajectoryMeasure.map projection = deterministicSource.trajectoryMeasure := by
    simpa [source, deterministicSource, projection] using
      (exploratorySource_trajectoryMeasure_map_knownRewardEpisodeBatchTrajectory
        rewardSource initialTable defaultState countRadius explorationRate
          (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n))
  refine ⟨hdeterministicMeasurable.preimage hprojection, ?_, ?_⟩
  · calc
      source.trajectoryMeasure countBadEvent =
          (source.trajectoryMeasure.map projection) deterministicBad := by
        rw [Measure.map_apply hprojection hdeterministicMeasurable]
      _ = deterministicSource.trajectoryMeasure deterministicBad := by
        rw [htrajectoryMap]
      _ <= ENNReal.ofReal delta := hdeterministicTail
  · intro trajectory htrajectory
    have hprojected : projection trajectory ∉ deterministicBad := by
      simpa [countBadEvent] using htrajectory
    have hgood := hdeterministicGood (projection trajectory) hprojected
    refine ⟨hgood.1, ?_⟩
    rw [exploratorySource_successorExpectedAverageRegret_eq_projected]
    exact hgood.2

/-- Stochastic realized-regret violation set for one scheduled window. -/
noncomputable def decayingExplorationAverageRealizedBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (rewardVarianceProxy : NNReal) (n : Nat) :
    Set
      (StochasticEpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)) := by
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
  exact {trajectory |
    AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor rewardVarianceProxy n <
      source.realizedSuccessorAverageRegret trajectory rounds}

/--
One stochastic finite window: projected counts and globally centered returns
cover the realized-regret violation set under the two-share scheduled budget.
-/
theorem exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real) (n : Nat)
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [Nonempty
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [Nonempty
      (StochasticEpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [StandardBorelSpace
      (StochasticEpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
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
    decayingExplorationAverageRealizedBehaviorRegretViolationSet mdp initialState
      rewardSource initialTable defaultState baseVisitFloor rewardVarianceProxy n
  let Good : StochasticEpisodeBatchTrajectory mdp episodes -> Prop := fun trajectory =>
    forall round : Fin rounds, forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        (adaptiveCumulativeEmpiricalOptimisticPlanAt
          (projection trajectory) defaultState countRadius round
          ).upperValueRemaining mdp.horizon le_rfl state
  have hcount :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n rewardSource initialTable defaultState
        support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcount
  rcases hcount with ⟨hcountMeasurable, hcountTail, hcountOutside⟩
  have hcountGood : forall trajectory, trajectory ∉ countBadEvent ->
      Good trajectory /\
        source.successorExpectedAverageRegret trajectory rounds <=
          AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
            mdp baseVisitFloor n := by
    intro trajectory htrajectory
    simpa [source, projection, countBadEvent, Good] using
      hcountOutside trajectory htrajectory
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes := by
    unfold episodes AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    exact
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes_pos
        _ _ _ _
  have htotal : 0 <
      ((AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp rounds episodes 1 rewardVarianceProxy : NNReal) : Real) := by
    rw [AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy_coe]
    have hbase : 0 <
        mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 rewardVarianceProxy :=
      mdp.globalReturnDeviationPerEpisodeVarianceProxy_pos 1 rewardVarianceProxy
        (by norm_num) hhorizon
    positivity
  have htransport :=
    source.trajectoryMeasure_expected_to_realized_successor_average_regret_transport_two_delta
      rounds hrounds hepisodes 1 rewardVarianceProxy hrewardBound law htotal
      delta delta
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
      countBadEvent
      (AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        mdp baseVisitFloor n)
      Good hcountMeasurable hcountTail hcountGood
  have hterminal :
      MeasurableSet combinedBadEvent /\
        source.trajectoryMeasure combinedBadEvent <=
          AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n /\
        forall trajectory, trajectory ∉ combinedBadEvent ->
          Good trajectory /\
            source.realizedSuccessorAverageRegret trajectory rounds <=
              AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
                mdp baseVisitFloor rewardVarianceProxy n := by
    simpa [returnBadEvent, combinedBadEvent,
      AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget,
      AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound,
      AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius,
      add_assoc] using htransport
  rcases hterminal with ⟨hmeasurable, htail, houtside⟩
  have hsubset : violationSet ⊆ combinedBadEvent := by
    intro trajectory hviolation
    by_contra htrajectory
    have hbound := (houtside trajectory htrajectory).2
    have hviolation' :
        AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor rewardVarianceProxy n <
          source.realizedSuccessorAverageRegret trajectory rounds := by
      simpa [violationSet,
        decayingExplorationAverageRealizedBehaviorRegretViolationSet,
        rounds, delta, explorationRate, visitFloor, episodes, countRadius,
        source] using hviolation
    exact (not_lt_of_ge hbound) hviolation'
  have hviolationTail :
      source.trajectoryMeasure violationSet <=
        AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n :=
    (measure_mono hsubset).trans htail
  exact ⟨hmeasurable, htail, hsubset, hviolationTail, by
    intro trajectory htrajectory
    simpa [Good] using houtside trajectory htrajectory⟩

/--
All scheduled stochastic windows plus the joint scalar limit. The indexed
Borel witnesses expose the changing deterministic and stochastic sample spaces.
-/
theorem exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_decayingExplorationAverageRealizedBehaviorConsistency_allWindows
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (hdetBatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (hdetTrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (hstochasticBatchBorel : forall n, StandardBorelSpace
      (StochasticEpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (hstochasticTrajectoryBorel : forall n, StandardBorelSpace
      (StochasticEpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
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
        letI : StandardBorelSpace
            (EpisodeBatch mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := hdetBatchBorel n
        letI : StandardBorelSpace
            (EpisodeBatchTrajectory mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := hdetTrajectoryBorel n
        letI : StandardBorelSpace
            (StochasticEpisodeBatch mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := hstochasticBatchBorel n
        letI : StandardBorelSpace
            (StochasticEpisodeBatchTrajectory mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := hstochasticTrajectoryBorel n
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
    letI := hdetBatchBorel n
    letI := hdetTrajectoryBorel n
    letI := hstochasticBatchBorel n
    letI := hstochasticTrajectoryBorel n
    exact
      exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency
        mdp initialState baseVisitFloor n rewardSource rewardVarianceProxy law
          initialTable defaultState support hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor

end AdaptiveCumulativeStochasticEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
