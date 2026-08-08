import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceL1Consistency
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Natural-causal almost-sure consistency

This module upgrades the heterogeneous natural-causal realized-regret process
from `L1` convergence to almost-sure convergence.  The proof keeps the same
dependent trajectory measure.  It applies the first Borel-Cantelli lemma to
the summable coordinate model events and to the mass-adapted successor-return
events, then consumes the existing fixed-burn-in absolute-regret envelope.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof

/-- The stretched-exponential sequence `exp (-sqrt n)` is summable. -/
theorem summable_exp_neg_sqrt_natCast :
    Summable (fun n : Nat => Real.exp (-Real.sqrt (n : Real))) := by
  let f : Nat -> Real := fun n => Real.exp (-Real.sqrt (n : Real))
  let u : Nat -> Nat := fun n => (n + 1) ^ 2
  have hf_nonneg : forall n, 0 <= f n := fun n => Real.exp_nonneg _
  have hf_antitone : forall {m n : Nat}, 0 < m -> m <= n -> f n <= f m := by
    intro m n _hm hmn
    apply Real.exp_monotone
    exact neg_le_neg (Real.sqrt_le_sqrt (by exact_mod_cast hmn))
  have hu_pos : forall n, 0 < u n := fun n => by
    dsimp [u]
    positivity
  have hu_strict : StrictMono u := by
    intro m n hmn
    dsimp [u]
    exact pow_lt_pow_left₀ (by omega) (by omega) (by omega)
  have hu_diff : SuccDiffBounded 3 u := by
    intro n
    have hleft : (n + 2 + 1) ^ 2 = (n + 1 + 1) ^ 2 + (2 * n + 5) := by ring
    have hright : (n + 1 + 1) ^ 2 = (n + 1) ^ 2 + (2 * n + 3) := by ring
    dsimp [u]
    omega
  apply (summable_schlomilch_iff_of_nonneg hf_nonneg (@hf_antitone) hu_pos
    hu_strict (by norm_num) hu_diff).1
  have hexp : Summable (fun n : Nat => Real.exp (-n)) :=
    Real.summable_exp_neg_nat
  have hnexp : Summable (fun n : Nat => (n : Real) * Real.exp (-n)) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 1 one_pos
  have hbase : Summable
      (fun n : Nat => (2 * (n : Real) + 3) * Real.exp (-n)) := by
    exact ((hnexp.mul_left 2).add (hexp.mul_left 3)).congr fun n => by ring
  have hmajor : Summable
      (fun n : Nat => (2 * (n : Real) + 3) * Real.exp (-((n : Real) + 1))) := by
    exact (hbase.mul_left (Real.exp (-1))).congr fun n => by
      rw [show Real.exp (-((n : Real) + 1)) = Real.exp (-1) * Real.exp (-n) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
  apply hmajor.congr
  intro n
  dsimp [u, f]
  rw [show (((n + 1 + 1) ^ 2 : Nat) : Real) - (((n + 1) ^ 2 : Nat) : Real) =
      2 * (n : Real) + 3 by push_cast; ring]
  rw [show Real.sqrt ((((n + 1) ^ 2 : Nat) : Real)) = (n : Real) + 1 by
    push_cast
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity]

namespace FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

/-- Positive episode batches make successor mass dominate the round index. -/
theorem natCast_le_successorEpisodeMass
    (episodes : Nat -> Nat) (hepisodes : forall t, 0 < episodes t)
    (rounds : Nat) :
    (rounds : Real) <= successorEpisodeMass episodes rounds := by
  rw [successorEpisodeMass_eq_sum_range]
  calc
    (rounds : Real) = (Finset.range rounds).sum (fun _ => (1 : Real)) := by simp
    _ <= (Finset.range rounds).sum (fun t => (episodes (t + 1) : Real)) := by
      apply Finset.sum_le_sum
      intro t _ht
      exact_mod_cast hepisodes (t + 1)

/-- A mass-adapted `exp (-sqrt mass)` schedule is summable. -/
theorem summable_exp_neg_sqrt_successorEpisodeMass
    (episodes : Nat -> Nat) (hepisodes : forall t, 0 < episodes t) :
    Summable (fun rounds =>
      Real.exp (-Real.sqrt (successorEpisodeMass episodes rounds))) := by
  refine summable_exp_neg_sqrt_natCast.of_nonneg_of_le
    (fun _ => Real.exp_nonneg _) ?_
  intro rounds
  apply Real.exp_monotone
  apply neg_le_neg
  exact Real.sqrt_le_sqrt
    (natCast_le_successorEpisodeMass episodes hepisodes rounds)

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The natural-causal mass-adapted return failure schedule is summable. -/
theorem summable_selfConsistentScheduledCausalVanishingReturnDelta
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Summable
      (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
        baseVisitFloor) := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  simpa [selfConsistentScheduledCausalVanishingReturnDelta, episodes] using
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.summable_exp_neg_sqrt_successorEpisodeMass
      episodes (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor t)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The return-failure ENNReal budget is finite. -/
theorem tsum_selfConsistentScheduledCausalVanishingReturnFailureBudget_ne_top
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    (∑' rounds, ENNReal.ofReal
      (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
        baseVisitFloor rounds)) ≠ ∞ :=
  (summable_selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
    baseVisitFloor).tsum_ofReal_ne_top

/-- The actual return-deviation event charged by the summable mass schedule. -/
noncomputable def selfConsistentScheduledCausalVanishingReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  selfConsistentScheduledCausalSuccessorReturnBadEvent mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor rounds
      (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
        baseVisitFloor rounds)

/-- Each event in the summable return schedule is measurable. -/
theorem measurableSet_selfConsistentScheduledCausalVanishingReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    MeasurableSet
      (selfConsistentScheduledCausalVanishingReturnBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          rounds) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, selfConsistentScheduledCausalSource]
    infer_instance
  simpa [source, selfConsistentScheduledCausalVanishingReturnBadEvent,
    selfConsistentScheduledCausalSuccessorReturnBadEvent] using
    source.measurableSet_successorGlobalReturnDeviationBadEvent rounds 1
      varianceProxy
        (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
          baseVisitFloor rounds)

/-- Every return event is bounded by its mass-adapted failure share. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_vanishingReturnBadEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (rounds : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledCausalVanishingReturnBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            rounds) <=
      ENNReal.ofReal
        (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
          baseVisitFloor rounds) := by
  dsimp only
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, selfConsistentScheduledCausalSource]
    infer_instance
  cases rounds with
  | zero =>
      have hle : source.trajectoryMeasure
          (selfConsistentScheduledCausalVanishingReturnBadEvent mdp initialState
            rewardSource initialTable defaultState varianceProxy baseVisitFloor 0) <= 1 :=
        calc
          source.trajectoryMeasure
              (selfConsistentScheduledCausalVanishingReturnBadEvent mdp initialState
                rewardSource initialTable defaultState varianceProxy baseVisitFloor 0) <=
              source.trajectoryMeasure Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      simpa [selfConsistentScheduledCausalVanishingReturnDelta,
        HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_eq_sum_range]
        using hle
  | succ rounds =>
      have hepisodes : forall t, 0 < episodes t := fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor t
      have htotal : 0 <
          ((HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp episodes (rounds + 1) 1 varianceProxy : NNReal) : Real) :=
        HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy_pos
          mdp episodes (rounds + 1) 1 varianceProxy (by omega) hepisodes
            hhorizon hvarianceProxy
      have hrewardBoundNN : forall state action,
          |mdp.reward state action| <= ((1 : NNReal) : Real) := by
        simpa using hrewardBound
      simpa [source, episodes,
        selfConsistentScheduledCausalVanishingReturnBadEvent,
        selfConsistentScheduledCausalSuccessorReturnBadEvent] using
        source.trajectoryMeasure_successorGlobalReturnDeviationBadEvent_le
          (rounds + 1) 1 varianceProxy hrewardBoundNN law htotal
          (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
            baseVisitFloor (rounds + 1))
          (selfConsistentScheduledCausalVanishingReturnDelta_pos mdp
            varianceProxy baseVisitFloor (rounds + 1))
          (selfConsistentScheduledCausalVanishingReturnDelta_le_one mdp
            varianceProxy baseVisitFloor (rounds + 1))

/-- The actual coordinate-model event measures have finite total mass. -/
theorem tsum_selfConsistentScheduledCausalModelRoundBadEvent_measure_ne_top
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (∑' t, source.trajectoryMeasure
      (selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor t)) ≠ ∞ := by
  dsimp only
  exact ne_top_of_le_ne_top
    (tsum_selfConsistentScheduledCausalCoordinateModelFailureBudget_ne_top mdp)
    (ENNReal.tsum_le_tsum fun t =>
      selfConsistentScheduledCausalSource_trajectoryMeasure_modelRoundBadEvent_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState baseVisitFloor t)

/-- The actual return-event measures have finite total mass. -/
theorem tsum_selfConsistentScheduledCausalVanishingReturnBadEvent_measure_ne_top
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (∑' rounds, source.trajectoryMeasure
      (selfConsistentScheduledCausalVanishingReturnBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          rounds)) ≠ ∞ := by
  dsimp only
  exact ne_top_of_le_ne_top
    (tsum_selfConsistentScheduledCausalVanishingReturnFailureBudget_ne_top mdp
      varianceProxy baseVisitFloor)
    (ENNReal.tsum_le_tsum fun rounds =>
      selfConsistentScheduledCausalSource_trajectoryMeasure_vanishingReturnBadEvent_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState baseVisitFloor hrewardBound hhorizon rounds)

/-
First Borel-Cantelli is applied twice on the same dependent trajectory space.
Only summability is used; no independence between rounds is introduced.
-/
/-- Almost every natural-causal trajectory is eventually model-good and return-good. -/
theorem ae_eventually_not_mem_selfConsistentScheduledCausalModel_and_returnBadEvents
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      (∀ᶠ t in atTop,
        trajectory ∉ selfConsistentScheduledCausalModelRoundBadEvent mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t) ∧
      (∀ᶠ rounds in atTop,
        trajectory ∉ selfConsistentScheduledCausalVanishingReturnBadEvent mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hmodel : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      ∀ᶠ t in atTop,
        trajectory ∉ selfConsistentScheduledCausalModelRoundBadEvent mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t :=
    ae_eventually_notMem
      (tsum_selfConsistentScheduledCausalModelRoundBadEvent_measure_ne_top
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState baseVisitFloor)
  have hreturn : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      ∀ᶠ rounds in atTop,
        trajectory ∉ selfConsistentScheduledCausalVanishingReturnBadEvent mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds :=
    ae_eventually_notMem
      (tsum_selfConsistentScheduledCausalVanishingReturnBadEvent_measure_ne_top
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState baseVisitFloor hrewardBound hhorizon)
  filter_upwards [hmodel, hreturn] with trajectory htrajectoryModel htrajectoryReturn
  exact ⟨htrajectoryModel, htrajectoryReturn⟩

/-- Almost every trajectory eventually obeys one fixed-burn-in regret envelope. -/
theorem ae_eventually_abs_selfConsistentScheduledNaturalCausalRealizedRegret_le_envelope
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      ∃ burnin, ∀ᶠ rounds in atTop,
        |selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory| <=
          selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope mdp
            varianceProxy baseVisitFloor burnin rounds := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hgood :=
    ae_eventually_not_mem_selfConsistentScheduledCausalModel_and_returnBadEvents
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState baseVisitFloor hrewardBound hhorizon
  filter_upwards [hgood] with trajectory htrajectory
  obtain ⟨burnin, hmodel⟩ := eventually_atTop.1 htrajectory.1
  refine ⟨burnin, ?_⟩
  filter_upwards [eventually_ge_atTop (max burnin 1), htrajectory.2] with
    rounds hroundsLarge hreturn
  have hburnin : burnin <= rounds :=
    le_trans (Nat.le_max_left burnin 1) hroundsLarge
  have hrounds : 0 < rounds :=
    lt_of_lt_of_le (by omega : 0 < max burnin 1) hroundsLarge
  have hnotTail : trajectory ∉
      selfConsistentScheduledCausalTailModelBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          burnin := by
    intro htail
    rw [selfConsistentScheduledCausalTailModelBadEvent] at htail
    simp only [Set.mem_iUnion] at htail
    obtain ⟨t, ht⟩ := htail
    have htBurnin : burnin <= t := by
      have htNotLt : ¬ (t : Nat) < burnin := by
        simpa [Finset.mem_range] using t.property
      omega
    exact hmodel t htBurnin ht
  have hnotEvent : trajectory ∉
      selfConsistentScheduledCausalTailModelReturnBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          burnin rounds := by
    rw [selfConsistentScheduledCausalTailModelReturnBadEvent, Set.mem_union,
      not_or]
    exact ⟨hnotTail, by
      simpa [selfConsistentScheduledCausalVanishingReturnBadEvent] using hreturn⟩
  have hterminal :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_tail_optimism_and_absoluteRealizedRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor burnin rounds hburnin hrounds
  dsimp only at hterminal
  simpa [selfConsistentScheduledNaturalCausalRealizedRegretProcess, source] using
    (hterminal.2.2 trajectory hnotEvent).2

/-
Terminal route theorem.  The process remains on the original heterogeneous
dependent trajectory measure.  Summable model and return events provide one
trajectory-dependent finite burn-in; the deterministic envelope then vanishes.
-/
/-- Natural-causal realized successor-average regret converges almost surely. -/
theorem selfConsistentScheduledCausalSource_realizedRegret_tendstoAlmostEverywhere_zero
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (forall rounds,
      Measurable
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)) ∧
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto
          (fun rounds =>
            selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory)
          atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  refine ⟨fun rounds =>
    measurable_selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds, ?_⟩
  have henvelope :=
    ae_eventually_abs_selfConsistentScheduledNaturalCausalRealizedRegret_le_envelope
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor
  filter_upwards [henvelope] with trajectory htrajectory
  obtain ⟨burnin, hbound⟩ := htrajectory
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have henvelopeSmall : ∀ᶠ rounds in atTop,
      selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope mdp
        varianceProxy baseVisitFloor burnin rounds < epsilon :=
    (tendsto_order.1
      (selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope_tendsto_zero
        mdp varianceProxy baseVisitFloor burnin)).2 epsilon hepsilon
  exact eventually_atTop.1 (by
    filter_upwards [hbound, henvelopeSmall] with rounds hroundsBound hroundsSmall
    simpa [Real.dist_eq] using lt_of_le_of_lt hroundsBound hroundsSmall)

/-
The final joint certificate keeps both consequences of each eventually
model-good coordinate.  In particular, the all-state optimism and recommended
policy regret certificate hold on the same full-measure set as realized-regret
convergence; no intersection of unrelated trajectory spaces is used.
-/
/-- Almost surely, late empirical models are optimistic while realized regret vanishes. -/
theorem selfConsistentScheduledCausalSource_eventually_modelOptimistic_and_realizedRegret_tendstoAlmostEverywhere_zero
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let episodes := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor t
    let rewardBudget := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor t
    let transitionBudget := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor t
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (forall rounds,
      Measurable
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)) ∧
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        (∀ᶠ t in atTop,
          let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
              (episodes t)
              (mdp.sampledEpisodeBatchOfStochasticTrajectories
                (episodes t) (trajectory t))
              defaultState (rewardBudget t) (transitionBudget t)
          (forall state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state <=
                model.plan.upperValueRemaining mdp.horizon le_rfl state) ∧
            model.plan.optimisticPolicy.expectedRegret initialState <=
              model.plan.optimisticPolicy.occupancySumRemaining
                (fun remaining hremaining state =>
                  2 * model.plan.selectedRadiusRemaining remaining hremaining state)
                mdp.horizon le_rfl initialState) ∧
        Tendsto
          (fun rounds =>
            selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory)
          atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hregret :=
    selfConsistentScheduledCausalSource_realizedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor
  have hgood :=
    ae_eventually_not_mem_selfConsistentScheduledCausalModel_and_returnBadEvents
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState baseVisitFloor hrewardBound hhorizon
  refine ⟨hregret.1, ?_⟩
  filter_upwards [hgood, hregret.2] with trajectory htrajectory htrajectoryRegret
  refine ⟨?_, htrajectoryRegret⟩
  filter_upwards [htrajectory.1] with t ht
  exact
    selfConsistentScheduledCausalSource_coordinateConfidence_of_not_mem_modelRoundBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor trajectory t ht

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end FiniteHorizonRL

end BanditRLProof
