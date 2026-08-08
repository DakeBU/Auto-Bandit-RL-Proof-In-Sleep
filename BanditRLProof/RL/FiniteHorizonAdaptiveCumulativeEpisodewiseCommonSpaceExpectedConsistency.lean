import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceConsistency
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Common-space expected absolute realized consistency

This module strengthens the independent-coordinate common-space convergence in
probability theorem to convergence of expected absolute realized-behavior
regret.  The additional input is an almost-everywhere deterministic envelope:
generated adaptive batches are reward-consistent, so every scheduled realized
average regret has absolute value at most twice the horizon.

The common space remains the product coupling of complete finite-window
experiments.  Nothing here constructs a nested causal online stream across
schedules or proves pathwise, almost-sure, or anytime consistency.
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

namespace MDP

/-- A deterministic finite trajectory has return bounded by the horizon. -/
theorem abs_cumulativeReward_le_horizon
    (mdp : MDP State Action)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (trajectory : Prod State (StepTrace Action State mdp.horizon)) :
    |mdp.cumulativeReward trajectory| <= (mdp.horizon : Real) := by
  rw [cumulativeReward, cumulativeRewardFrom_eq_sum_traceReward]
  calc
    |∑ stage : Fin mdp.horizon,
        mdp.reward
          (traceStateAtFrom trajectory.1 trajectory.2 stage)
          (trajectory.2 stage).1| <=
        ∑ stage : Fin mdp.horizon,
          |mdp.reward
            (traceStateAtFrom trajectory.1 trajectory.2 stage)
            (trajectory.2 stage).1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _stage : Fin mdp.horizon, (1 : Real) := by
      apply Finset.sum_le_sum
      intro stage _hstage
      exact hrewardBound _ _
    _ = (mdp.horizon : Real) := by simp

end MDP

namespace AdaptiveEpisodeBatchSource

/-- The optimal initial expected return inherits the deterministic horizon envelope. -/
theorem abs_optimalInitialExpectedReturn_le_horizon
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    |optimalInitialExpectedReturn mdp initialState| <= (mdp.horizon : Real) := by
  unfold optimalInitialExpectedReturn
  rw [← mdp.optimalPolicy_valueAt_eq_optimalValueAt]
  rw [← mdp.optimalPolicy.integral_cumulativeReward_trajectoryMeasure_eq_integral_valueAt_zero]
  rw [← Real.norm_eq_abs]
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := mdp.optimalPolicy.trajectoryMeasure initialState)
    (C := (mdp.horizon : Real))
    (Filter.Eventually.of_forall fun trajectory => by
      rw [Real.norm_eq_abs]
      exact mdp.abs_cumulativeReward_le_horizon hrewardBound trajectory)
  simpa using hnorm

omit [DecidableEq State] [DecidableEq Action] [Nonempty State] [Nonempty Action] in
/-- Every adaptive successor batch is reward-consistent almost everywhere. -/
theorem trajectoryMeasure_successor_rewardConsistent_ae
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      (trajectory (n + 1)).RewardConsistent := by
  let prefixMeasure :=
    source.trajectoryMeasure.map (Preorder.frestrictLe n)
  let pairMap : EpisodeBatchTrajectory mdp episodes ->
      Prod (EpisodeBatchPrefix mdp episodes n) (EpisodeBatch mdp episodes) :=
    fun trajectory =>
      (Preorder.frestrictLe n trajectory, trajectory (n + 1))
  have hpairMap : Measurable pairMap := by fun_prop
  have hpair : ∀ᵐ pair ∂prefixMeasure ⊗ₘ source.batchKernel n,
      pair.2.RewardConsistent := by
    apply Measure.ae_compProd_of_ae_ae
      (EpisodeBatch.measurableSet_rewardConsistent.preimage measurable_snd)
    exact Filter.Eventually.of_forall fun history => by
      rw [source.batchKernel_eq_iidEpisodeBatchMeasure]
      exact (source.successorPolicy n history).iidEpisodeBatchMeasure_rewardConsistent_ae
        initialState episodes
  have hpair' := hpair
  rw [source.trajectoryMeasure_prefix_compProd n] at hpair'
  have hpull := ae_of_ae_map hpairMap.aemeasurable hpair'
  simpa [pairMap] using hpull

/-- Reward-consistent successor batches give a uniform realized-average envelope. -/
theorem abs_realizedSuccessorAverageRegret_le_two_mul_horizon
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hconsistent : forall round : Fin rounds,
      (trajectory ((round : Nat) + 1)).RewardConsistent) :
    |source.realizedSuccessorAverageRegret trajectory rounds| <=
      2 * (mdp.horizon : Real) := by
  have hoptimal := abs_optimalInitialExpectedReturn_le_horizon
    mdp initialState hrewardBound
  have hepisodes_nonneg : 0 <= (episodes : Real) := by positivity
  have hterm : forall round : Fin rounds,
      |(episodes : Real) * optimalInitialExpectedReturn mdp initialState -
          EpisodeBatch.totalReturn (trajectory ((round : Nat) + 1))| <=
        2 * (episodes : Real) * (mdp.horizon : Real) := by
    intro round
    calc
      |(episodes : Real) * optimalInitialExpectedReturn mdp initialState -
          EpisodeBatch.totalReturn (trajectory ((round : Nat) + 1))| <=
          |(episodes : Real) * optimalInitialExpectedReturn mdp initialState| +
            |EpisodeBatch.totalReturn
              (trajectory ((round : Nat) + 1))| := abs_sub _ _
      _ = (episodes : Real) *
            |optimalInitialExpectedReturn mdp initialState| +
            |EpisodeBatch.totalReturn
              (trajectory ((round : Nat) + 1))| := by
          rw [abs_mul, abs_of_nonneg hepisodes_nonneg]
      _ <= (episodes : Real) * (mdp.horizon : Real) +
            (episodes : Real) * (mdp.horizon : Real) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hoptimal hepisodes_nonneg)
            (EpisodeBatch.abs_totalReturn_le_of_rewardConsistent
              _ (hconsistent round) hrewardBound)
      _ = 2 * (episodes : Real) * (mdp.horizon : Real) := by ring
  have hcumulative :
      |source.realizedSuccessorCumulativeRegret trajectory rounds| <=
        ∑ _round : Fin rounds,
          2 * (episodes : Real) * (mdp.horizon : Real) := by
    unfold realizedSuccessorCumulativeRegret
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun round _ => hterm round)
  have hdenom : 0 < (episodes : Real) * (rounds : Real) := by positivity
  rw [realizedSuccessorAverageRegret, abs_div, abs_of_pos hdenom]
  calc
    |source.realizedSuccessorCumulativeRegret trajectory rounds| /
        ((episodes : Real) * (rounds : Real)) <=
      (∑ _round : Fin rounds,
          2 * (episodes : Real) * (mdp.horizon : Real)) /
        ((episodes : Real) * (rounds : Real)) :=
      div_le_div_of_nonneg_right hcumulative hdenom.le
    _ = 2 * (mdp.horizon : Real) := by
      simp
      field_simp

/-- The adaptive realized average has the `2H` envelope almost everywhere. -/
theorem trajectoryMeasure_abs_realizedSuccessorAverageRegret_le_two_mul_horizon_ae
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      |source.realizedSuccessorAverageRegret trajectory rounds| <=
        2 * (mdp.horizon : Real) := by
  have hconsistent : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      forall round : Fin rounds,
        (trajectory ((round : Nat) + 1)).RewardConsistent :=
    Filter.eventually_all.2 fun round =>
      source.trajectoryMeasure_successor_rewardConsistent_ae (round : Nat)
  filter_upwards [hconsistent] with trajectory htrajectory
  exact source.abs_realizedSuccessorAverageRegret_le_two_mul_horizon
    trajectory rounds hrounds hepisodes hrewardBound htrajectory

/-- The adaptive realized successor-average regret is integrable. -/
theorem integrable_realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    Integrable (fun trajectory =>
      source.realizedSuccessorAverageRegret trajectory rounds)
      source.trajectoryMeasure := by
  refine Integrable.mono' (integrable_const (2 * (mdp.horizon : Real)))
    (source.measurable_realizedSuccessorAverageRegret rounds).aestronglyMeasurable ?_
  filter_upwards [
    source.trajectoryMeasure_abs_realizedSuccessorAverageRegret_le_two_mul_horizon_ae
      rounds hrounds hepisodes hrewardBound] with trajectory htrajectory
  exact htrajectory

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/-- The common-space regret process has the deterministic `2H` envelope a.e. -/
theorem decayingExplorationEpisodewiseCommonMeasure_abs_realizedBehaviorRegretProcess_le_two_mul_horizon_ae
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    ∀ᵐ omega ∂decayingExplorationEpisodewiseCommonMeasure mdp initialState
        initialTable defaultState baseVisitFloor,
      |decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n omega| <=
        2 * (mdp.horizon : Real) := by
  let source := decayingExplorationEpisodewiseWindowSource mdp initialState
    initialTable defaultState baseVisitFloor n
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    mdp baseVisitFloor n
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes :=
    AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes_pos
      mdp baseVisitFloor n
  have hwindow : ∀ᵐ trajectory ∂
      decayingExplorationEpisodewiseWindowMeasure mdp initialState initialTable
        defaultState baseVisitFloor n,
      |source.realizedSuccessorAverageRegret trajectory rounds| <=
        2 * (mdp.horizon : Real) := by
    simpa [source, rounds, episodes,
      decayingExplorationEpisodewiseWindowMeasure] using
      source.trajectoryMeasure_abs_realizedSuccessorAverageRegret_le_two_mul_horizon_ae
        rounds hrounds hepisodes hrewardBound
  rw [← decayingExplorationEpisodewiseCommonMeasure_map_eval mdp initialState
    initialTable defaultState baseVisitFloor n] at hwindow
  have hpull := ae_of_ae_map (measurable_pi_apply n).aemeasurable hwindow
  simpa [decayingExplorationEpisodewiseRealizedBehaviorRegretProcess,
    source, rounds] using hpull

/-- Every common-space regret coordinate is integrable. -/
theorem integrable_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    Integrable
      (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n)
      (decayingExplorationEpisodewiseCommonMeasure mdp initialState
        initialTable defaultState baseVisitFloor) := by
  refine Integrable.mono' (integrable_const (2 * (mdp.horizon : Real)))
    (measurable_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
      mdp initialState initialTable defaultState baseVisitFloor n).aestronglyMeasurable ?_
  filter_upwards [
    decayingExplorationEpisodewiseCommonMeasure_abs_realizedBehaviorRegretProcess_le_two_mul_horizon_ae
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound n]
    with omega homega
  exact homega

/-- The pulled-back sharp finite-window bad event is measurable on the common space. -/
theorem measurableSet_decayingExplorationEpisodewiseCommonBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    MeasurableSet
      (decayingExplorationEpisodewiseCommonBadEvent mdp initialState
        initialTable defaultState baseVisitFloor n) := by
  letI := hbatchBorel n
  letI := htrajectoryBorel n
  have hfinite :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationEpisodewiseAverageAbsoluteRealizedBehaviorConsistency
      mdp initialState baseVisitFloor n initialTable defaultState support
      hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨hmeasurable, _htail, _houtside⟩
  have hmeasurable' : MeasurableSet
      ((decayingExplorationEpisodewiseWindowSource mdp initialState initialTable
          defaultState baseVisitFloor n).adaptiveCumulativeCountBadEvent
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) ∪
        (decayingExplorationEpisodewiseWindowSource mdp initialState initialTable
          defaultState baseVisitFloor n).episodewiseSuccessorReturnDeviationBadEvent
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)) := by
    simpa [decayingExplorationEpisodewiseWindowSource] using hmeasurable
  unfold decayingExplorationEpisodewiseCommonBadEvent
  dsimp only
  exact hmeasurable'.preimage (measurable_pi_apply n)

/-- Expected absolute scheduled realized-behavior regret on the common space. -/
noncomputable def decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) : Real :=
  integral
    (decayingExplorationEpisodewiseCommonMeasure mdp initialState initialTable
      defaultState baseVisitFloor)
    (fun omega =>
      |decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n omega|)

/-- The deterministic good-event radius plus the uniform bad-event contribution. -/
noncomputable def decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Real :=
  AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
      mdp baseVisitFloor n +
    2 * (mdp.horizon : Real) *
      (AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n).toReal

/-- Expected absolute realized-behavior regret is nonnegative. -/
theorem decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    0 <= decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret
      mdp initialState initialTable defaultState baseVisitFloor n := by
  unfold decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret
  exact integral_nonneg fun _ => abs_nonneg _

/-- The explicit expected-absolute bound is nonnegative. -/
theorem decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound_nonneg
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    0 <= decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound
      mdp baseVisitFloor n := by
  unfold decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound
  exact add_nonneg
    (AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound_nonneg
      mdp hhorizon baseVisitFloor hbaseVisitFloor n)
    (by positivity)

/--
The common-space expected absolute regret is controlled by the sharp good-event
radius plus the uniform `2H` envelope times the failure probability.
-/
theorem decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret_le_bound
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret mdp
        initialState initialTable defaultState baseVisitFloor n <=
      decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound
        mdp baseVisitFloor n := by
  let mu := decayingExplorationEpisodewiseCommonMeasure mdp initialState
    initialTable defaultState baseVisitFloor
  let process := decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
    initialState initialTable defaultState baseVisitFloor n
  let bad := decayingExplorationEpisodewiseCommonBadEvent mdp initialState
    initialTable defaultState baseVisitFloor n
  let budget :=
    AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
      mdp baseVisitFloor n
  let envelope := 2 * (mdp.horizon : Real)
  let overflow : DecayingExplorationEpisodewiseWindowSpace mdp baseVisitFloor ->
      Real := bad.indicator (fun _ => envelope)
  have hbad : MeasurableSet bad := by
    exact measurableSet_decayingExplorationEpisodewiseCommonBadEvent
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor n
  have hprocess : Integrable process mu := by
    exact integrable_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound n
  have hgap : Integrable (fun omega => |process omega|) mu := hprocess.abs
  have hoverflow : Integrable overflow mu := by
    exact (integrable_const envelope).indicator hbad
  have hbudget : 0 <= budget := by
    exact
      AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound_nonneg
        mdp hhorizon baseVisitFloor hbaseVisitFloor n
  have henvelope : ∀ᵐ omega ∂mu, |process omega| <= envelope := by
    exact
      decayingExplorationEpisodewiseCommonMeasure_abs_realizedBehaviorRegretProcess_le_two_mul_horizon_ae
        mdp initialState initialTable defaultState baseVisitFloor hrewardBound n
  have hpoint : ∀ᵐ omega ∂mu,
      |process omega| <= budget + overflow omega := by
    filter_upwards [henvelope] with omega homegaEnvelope
    by_cases homega : omega ∈ bad
    · calc
        |process omega| <= envelope := homegaEnvelope
        _ <= budget + envelope := le_add_of_nonneg_left hbudget
        _ = budget + overflow omega := by
          simp [overflow, Set.indicator_of_mem homega]
    · have hgood :=
        abs_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_le_of_not_mem_badEvent
          mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel
          initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor n omega (by simpa [bad] using homega)
      calc
        |process omega| <= budget := by simpa [process, budget] using hgood
        _ = budget + overflow omega := by
          simp [overflow, Set.indicator_of_notMem homega]
  have htail :=
    decayingExplorationEpisodewiseCommonMeasure_badEvent_le
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor n
  have htailReal : mu.real bad <=
      (AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n).toReal := by
    rw [Measure.real]
    exact ENNReal.toReal_mono
      (by
        simp [AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget])
      (by simpa [mu, bad] using htail)
  have henvelope_nonneg : 0 <= envelope := by
    dsimp [envelope]
    positivity
  change integral mu (fun omega => |process omega|) <=
    budget + envelope *
      (AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n).toReal
  calc
    integral mu (fun omega => |process omega|) <=
        integral mu (fun omega => budget + overflow omega) :=
      integral_mono_ae hgap ((integrable_const budget).add hoverflow) hpoint
    _ = budget + integral mu overflow := by
      rw [integral_add (integrable_const budget) hoverflow, integral_const]
      simp [MeasureTheory.probReal_univ]
    _ = budget + envelope * mu.real bad := by
      congr 1
      change integral mu (bad.indicator (fun _omega => envelope)) =
        envelope * mu.real bad
      rw [integral_indicator hbad, setIntegral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]
    _ <= budget + envelope *
        (AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n).toReal :=
      add_le_add (le_refl budget)
        (mul_le_mul_of_nonneg_left htailReal henvelope_nonneg)

/-- The real-valued failure budget tends to zero. -/
theorem decayingExplorationRealizedFailureBudget_toReal_tendsto_zero :
    Tendsto
      (fun n =>
        (AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n).toReal)
      atTop (nhds 0) := by
  simpa using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget_tendsto_zero

/-- The explicit expected-absolute envelope tends to zero. -/
theorem decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound
        mdp baseVisitFloor) atTop (nhds 0) := by
  simpa [decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound]
    using
      (AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound_tendsto_zero
        mdp hhorizon baseVisitFloor hbaseVisitFloor).add
        (tendsto_const_nhds.mul
          decayingExplorationRealizedFailureBudget_toReal_tendsto_zero)

/--
Terminal expected-consistency theorem: all coordinates are integrable, every
finite expected absolute regret obeys the explicit bound, and those
expectations converge to zero.
-/
theorem exploratorySource_decayingExplorationEpisodewiseCommonMeasure_integrable_expectedAbsoluteRealizedBehaviorRegret_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    (forall n,
      Integrable
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
          initialState initialTable defaultState baseVisitFloor n)
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor)) /\
      (forall n,
        decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret mdp
            initialState initialTable defaultState baseVisitFloor n <=
          decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound
            mdp baseVisitFloor n) /\
      Tendsto
        (decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret mdp
          initialState initialTable defaultState baseVisitFloor)
        atTop (nhds 0) := by
  refine ⟨fun n =>
    integrable_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound n,
    fun n =>
      decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret_le_bound
        mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
        defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor n,
    ?_⟩
  apply squeeze_zero
  · intro n
    exact decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret_nonneg
      mdp initialState initialTable defaultState baseVisitFloor n
  · intro n
    exact decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret_le_bound
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor n
  · exact
      decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegretBound_tendsto_zero
        mdp hhorizon baseVisitFloor hbaseVisitFloor

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
