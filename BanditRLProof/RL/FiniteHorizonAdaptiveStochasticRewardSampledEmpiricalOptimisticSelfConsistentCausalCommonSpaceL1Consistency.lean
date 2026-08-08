import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceConsistency

/-!
# Natural causal L1 consistency for heterogeneous scheduled batches

This route strengthens the compiled convergence-in-probability theorem on the
single heterogeneous causal trajectory measure. It does not use the independent
product of complete finite-window experiments.

The expected selected-policy regret is uniformly bounded by `2 * horizon`.
After a fixed burn-in, the compiled model certificate controls its good-event
part, while the summable model tail pays the bounded bad-event contribution.
The globally centered sampled-return deviation is integrated directly from its
conditional sub-Gaussian MGF and divided by the actual successor episode mass.

Regularity is unchanged: finite nonempty Standard Borel State/Action spaces, a
probability initial law, positive horizon/base visit floor/reward proxy, bounded
stored means, a uniform mean-compatible selected-reward sub-Gaussian law, and
the existing full-exploration path floor.

Failure policy: preserve the one dependent causal source, actual coordinate
batch sizes, `n`-prefix to `n + 1` policy selection, successor-only initial
exclusion, global centering, and actual-mass normalization. No pathwise,
almost-sure, anytime, minimax, state-reachability, or complete UCB-VI statement
is inferred.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

/-- Every heterogeneous weighted selected-policy average is at most `2H`. -/
theorem successorWeightedExpectedAverageRegret_le_two_mul_horizon
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hmass : 0 < successorEpisodeMass episodes rounds)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    source.successorWeightedExpectedAverageRegret trajectory rounds <=
      2 * (mdp.horizon : Real) := by
  have hsum :
      source.successorWeightedExpectedCumulativeRegret trajectory rounds <=
        (2 * (mdp.horizon : Real)) * successorEpisodeMass episodes rounds := by
    unfold successorWeightedExpectedCumulativeRegret successorEpisodeMass
    calc
      (∑ round : Fin rounds,
          (episodes ((round : Nat) + 1) : Real) *
            (source.successorPolicyAt trajectory round).expectedRegret
              initialState) <=
          ∑ round : Fin rounds,
            (episodes ((round : Nat) + 1) : Real) *
              (2 * (mdp.horizon : Real)) := by
        apply Finset.sum_le_sum
        intro round _hround
        exact mul_le_mul_of_nonneg_left
          (MarkovPolicy.expectedRegret_le_two_mul_horizon_of_rewardBound
            (source.successorPolicyAt trajectory round) initialState
              hrewardBound)
          (by positivity)
      _ = (2 * (mdp.horizon : Real)) *
          ∑ round : Fin rounds,
            (episodes ((round : Nat) + 1) : Real) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro round _hround
        ring
  unfold successorWeightedExpectedAverageRegret
  calc
    source.successorWeightedExpectedCumulativeRegret trajectory rounds /
        successorEpisodeMass episodes rounds <=
      ((2 * (mdp.horizon : Real)) * successorEpisodeMass episodes rounds) /
        successorEpisodeMass episodes rounds :=
      div_le_div_of_nonneg_right hsum hmass.le
    _ = 2 * (mdp.horizon : Real) := by
      field_simp [ne_of_gt hmass]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- The heterogeneous successor deviation has one global sub-Gaussian MGF. -/
theorem trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_hasSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [forall n, StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, Nonempty
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes n))]
    [forall n, Nonempty (StochasticEpisodeBatch mdp (episodes n))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    HasSubgaussianMGF
      (source.cumulativeSuccessorGlobalReturnDeviation rounds)
      (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
        rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let F := Filtration.piLE
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | _ + 1 =>
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          (episodes t) rewardBound rewardVarianceProxy
  have hadapted : StronglyAdapted F
      source.successorGlobalReturnIncrement := by
    simpa [F] using source.successorGlobalReturnIncrement_stronglyAdapted_piLE
  have hzero : HasSubgaussianMGF
      (source.successorGlobalReturnIncrement 0) (cY 0)
      source.trajectoryMeasure := by
    change HasSubgaussianMGF (fun _ => 0) 0 source.trajectoryMeasure
    exact HasSubgaussianMGF.fun_zero
  have hsucc : forall i, i < (rounds + 1) - 1 ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (source.successorGlobalReturnIncrement (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.successorGlobalReturnIncrement_succ_hasCondSubgaussianMGF
        i rewardBound rewardVarianceProxy hrewardBound law
  simpa [cumulativeSuccessorGlobalReturnVarianceProxy,
    cumulativeSuccessorGlobalReturnDeviation, cY] using
    (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
      hadapted hzero (rounds + 1) hsucc)

/-- Finite-prefix heterogeneous realized successor-average regret is integrable. -/
theorem integrable_realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [forall n, StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, Nonempty
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes n))]
    [forall n, Nonempty (StochasticEpisodeBatch mdp (episodes n))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : forall t, 0 < episodes t)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (hrewardBoundOne : forall state action, |mdp.reward state action| <= 1)
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    Integrable (source.realizedSuccessorAverageRegret (rounds := rounds))
      source.trajectoryMeasure := by
  let expected := fun trajectory =>
    source.successorWeightedExpectedAverageRegret trajectory rounds
  let deviation := source.cumulativeSuccessorGlobalReturnDeviation rounds
  let mass := successorEpisodeMass episodes rounds
  have hmass : 0 < mass := by
    exact successorEpisodeMass_pos episodes rounds hrounds hepisodes
  have hdeviation : Integrable deviation source.trajectoryMeasure :=
    (source.trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_hasSubgaussianMGF
      rounds rewardBound rewardVarianceProxy hrewardBound law).integrable
  have hrealizedMeas : Measurable
      (source.realizedSuccessorAverageRegret (rounds := rounds)) :=
    source.measurable_realizedSuccessorAverageRegret rounds
  have hexpectedMeas : Measurable expected := by
    have heq : expected = fun trajectory =>
        source.realizedSuccessorAverageRegret trajectory rounds +
          deviation trajectory / mass := by
      funext trajectory
      rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
        trajectory rounds (by simpa [mass] using hmass)]
      simp [expected, deviation, mass]
    rw [heq]
    exact hrealizedMeas.add
      ((source.measurable_cumulativeSuccessorGlobalReturnDeviation rounds).div
        measurable_const)
  have hexpected : Integrable expected source.trajectoryMeasure := by
    apply Integrable.of_bound hexpectedMeas.aestronglyMeasurable
      (2 * (mdp.horizon : Real))
    exact Filter.Eventually.of_forall fun trajectory => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact source.successorWeightedExpectedAverageRegret_le_two_mul_horizon
          trajectory rounds (by simpa [mass] using hmass) hrewardBoundOne
      · exact source.successorWeightedExpectedAverageRegret_nonneg
          trajectory rounds
  have heq : source.realizedSuccessorAverageRegret (rounds := rounds) =
      fun trajectory => expected trajectory - deviation trajectory / mass := by
    funext trajectory
    exact source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
      trajectory rounds (by simpa [mass] using hmass)
  rw [heq]
  exact hexpected.sub (hdeviation.div_const mass)

/-- Direct first-moment envelope for the normalized heterogeneous deviation. -/
noncomputable def normalizedSuccessorGlobalReturnMGFFirstMomentBound
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : Real :=
  2 *
      Real.sqrt
        (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
          rewardBound rewardVarianceProxy : Real) *
      Real.exp (1 / 2 : Real) /
    successorEpisodeMass episodes rounds

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The normalized heterogeneous MGF first-moment envelope is nonnegative. -/
theorem normalizedSuccessorGlobalReturnMGFFirstMomentBound_nonneg
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) :
    0 <= normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp episodes
      rounds rewardBound rewardVarianceProxy := by
  unfold normalizedSuccessorGlobalReturnMGFFirstMomentBound
  apply div_nonneg (by positivity)
  unfold successorEpisodeMass
  exact Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A sufficiently wide normalized confidence radius dominates the MGF mean. -/
theorem normalizedSuccessorGlobalReturnMGFFirstMomentBound_le_confidenceRadius
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (delta : Real)
    (hmass : 0 < successorEpisodeMass episodes rounds)
    (hlog : (1 / 2 : Real) <= Real.log (2 / delta)) :
    normalizedSuccessorGlobalReturnMGFFirstMomentBound mdp episodes rounds
        rewardBound rewardVarianceProxy <=
      2 * Real.exp (1 / 2 : Real) *
        normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
          rewardBound rewardVarianceProxy delta := by
  let c : Real :=
    (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
      rewardBound rewardVarianceProxy : Real)
  let mass : Real := successorEpisodeMass episodes rounds
  have hc : 0 <= c := by positivity
  have hinside : c <= 2 * c * Real.log (2 / delta) := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hlog)]
  have hsqrt : Real.sqrt c <=
      Real.sqrt (2 * c * Real.log (2 / delta)) :=
    Real.sqrt_le_sqrt hinside
  unfold normalizedSuccessorGlobalReturnMGFFirstMomentBound
    normalizedSuccessorGlobalReturnConfidenceRadius
    Concentration.subGaussianSumConfidenceRadius
  dsimp [c, mass] at hsqrt hmass
  calc
    2 * Real.sqrt
          (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
            rewardBound rewardVarianceProxy : Real) *
          Real.exp (1 / 2 : Real) /
        successorEpisodeMass episodes rounds <=
      2 * Real.sqrt
          (2 *
            (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta)) *
          Real.exp (1 / 2 : Real) /
        successorEpisodeMass episodes rounds := by
      gcongr
    _ = 2 * Real.exp (1 / 2 : Real) *
        (Real.sqrt
          (2 *
            (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta)) /
          successorEpisodeMass episodes rounds) := by ring

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every post-burn-in model budget is finite. -/
theorem selfConsistentScheduledCausalTailModelFailureBudget_ne_top
    (mdp : MDP State Action) (burnin : Nat) :
    selfConsistentScheduledCausalTailModelFailureBudget mdp burnin ≠ ⊤ := by
  let f := selfConsistentScheduledCausalCoordinateModelFailureBudget mdp
  have hle : selfConsistentScheduledCausalTailModelFailureBudget mdp burnin <=
      tsum f := by
    unfold selfConsistentScheduledCausalTailModelFailureBudget
    simpa [f] using
      (ENNReal.tsum_mono_subtype f
        (s := {t | t ∉ Finset.range burnin})
        (t := Set.univ) (Set.subset_univ _))
  exact ne_top_of_le_ne_top
    (tsum_selfConsistentScheduledCausalCoordinateModelFailureBudget_ne_top mdp)
    hle

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The real-valued post-burn-in model tail also tends to zero. -/
theorem selfConsistentScheduledCausalTailModelFailureBudget_toReal_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto
      (fun burnin =>
        (selfConsistentScheduledCausalTailModelFailureBudget mdp burnin).toReal)
      atTop (nhds 0) := by
  simpa using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (selfConsistentScheduledCausalTailModelFailureBudget_tendsto_zero mdp)

/-- Scheduled direct-MGF contribution under actual successor mass. -/
noncomputable def selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnMGFFirstMomentBound
    mdp
      (fun t => AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor t)
      rounds 1 varianceProxy

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled direct-MGF contribution is nonnegative. -/
theorem selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
      varianceProxy baseVisitFloor rounds := by
  exact HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnMGFFirstMomentBound_nonneg
    mdp _ rounds 1 varianceProxy

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled direct-MGF first-moment contribution tends to zero. -/
theorem selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
        varianceProxy baseVisitFloor) atTop (nhds 0) := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  apply squeeze_zero
  · intro rounds
    exact selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound_nonneg
      mdp varianceProxy baseVisitFloor rounds
  · intro rounds
    show selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
        varianceProxy baseVisitFloor rounds <=
      2 * Real.exp (1 / 2 : Real) *
        selfConsistentScheduledCausalReturnRateEnvelope mdp varianceProxy
          baseVisitFloor rounds
    cases rounds with
    | zero =>
        simp [selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnMGFFirstMomentBound,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass]
        exact mul_nonneg (by positivity) (by
          unfold selfConsistentScheduledCausalReturnRateEnvelope
            HeterogeneousAdaptiveStochasticEpisodeBatchSource.fixedHalfSuccessorGlobalReturnRateEnvelope
          exact Real.sqrt_nonneg _)
    | succ rounds =>
        have hmass : 0 <
            HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
              episodes (rounds + 1) :=
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_pos
            episodes (rounds + 1) (by omega)
              (fun t =>
                AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
                  mdp varianceProxy baseVisitFloor t)
        have hlog : (1 / 2 : Real) <= Real.log (2 / (1 / 2 : Real)) := by
          have h := Real.le_log_one_add_of_nonneg
            (show (0 : Real) <= 3 by norm_num)
          norm_num at h
          linarith
        calc
          selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
              varianceProxy baseVisitFloor (rounds + 1) <=
            2 * Real.exp (1 / 2 : Real) *
              HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
                mdp episodes (rounds + 1) 1 varianceProxy (1 / 2) := by
              exact HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnMGFFirstMomentBound_le_confidenceRadius
                mdp episodes (rounds + 1) 1 varianceProxy (1 / 2) hmass hlog
          _ = 2 * Real.exp (1 / 2 : Real) *
              selfConsistentScheduledCausalReturnRateEnvelope mdp varianceProxy
                baseVisitFloor (rounds + 1) := by
            rw [HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius_half_eq
              mdp episodes (rounds + 1) 1 varianceProxy hmass]
            rfl
  · have hconst : Tendsto
        (fun _rounds : Nat => 2 * Real.exp (1 / 2 : Real)) atTop
        (nhds (2 * Real.exp (1 / 2 : Real))) := tendsto_const_nhds
    simpa using hconst.mul
      (selfConsistentScheduledCausalReturnRateEnvelope_tendsto_zero mdp
        varianceProxy baseVisitFloor)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The fixed-burn-in expected-regret envelope is nonnegative. -/
theorem selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) :
    0 <= selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
      varianceProxy baseVisitFloor burnin rounds := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  unfold selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope
  dsimp only
  apply add_nonneg
  · apply div_nonneg
    · apply mul_nonneg
      · positivity
      · unfold HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
        exact Finset.sum_nonneg fun _ _ => by positivity
    · unfold HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
      exact Finset.sum_nonneg fun _ _ => by positivity
  · unfold selfConsistentScheduledCausalWeightedPlanningRateEnvelope
      natWeightedAverage
    apply div_nonneg
    · exact Finset.sum_nonneg fun t _ => by
        apply mul_nonneg (by positivity)
        unfold selfConsistentScheduledCausalPlanningRateAt
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionContractionEnvelope
          exploratoryBehaviorRegretCharge
        positivity
    · exact Finset.sum_nonneg fun _ _ => by positivity

/-- Expected absolute regret of one natural causal prefix. -/
noncomputable def selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  integral source.trajectoryMeasure fun trajectory =>
    |selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
        rounds trajectory|

/-- Two-parameter direct `L1` envelope after a fixed model burn-in. -/
noncomputable def selfConsistentScheduledCausalBurninExpectedAbsoluteRegretL1Envelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) : Real :=
  selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
      varianceProxy baseVisitFloor burnin rounds +
    2 * (mdp.horizon : Real) *
      (selfConsistentScheduledCausalTailModelFailureBudget mdp burnin).toReal +
    selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
      varianceProxy baseVisitFloor rounds

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The direct natural-causal `L1` envelope is nonnegative. -/
theorem selfConsistentScheduledCausalBurninExpectedAbsoluteRegretL1Envelope_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) :
    0 <= selfConsistentScheduledCausalBurninExpectedAbsoluteRegretL1Envelope
      mdp varianceProxy baseVisitFloor burnin rounds := by
  unfold selfConsistentScheduledCausalBurninExpectedAbsoluteRegretL1Envelope
  exact add_nonneg
    (add_nonneg
      (selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope_nonneg
        mdp varianceProxy baseVisitFloor burnin rounds)
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg))
    (selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound_nonneg
      mdp varianceProxy baseVisitFloor rounds)

/-- Every coordinate of the natural causal realized-regret process is integrable. -/
theorem integrable_selfConsistentScheduledNaturalCausalRealizedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    Integrable
      (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
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
      have hzero :
          selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor 0 = fun _ => 0 := by
        funext trajectory
        simp [selfConsistentScheduledNaturalCausalRealizedRegretProcess,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.realizedSuccessorAverageRegret,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.realizedSuccessorCumulativeRegret,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass]
      rw [hzero]
      exact integrable_const 0
  | succ rounds =>
      have h :=
        HeterogeneousAdaptiveStochasticEpisodeBatchSource.integrable_realizedSuccessorAverageRegret
          source (rounds + 1) (by omega)
          (fun t =>
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
              mdp varianceProxy baseVisitFloor t)
          1 varianceProxy hrewardBound hrewardBound (by
            simpa [source, selfConsistentScheduledCausalSource] using law)
      simpa [selfConsistentScheduledNaturalCausalRealizedRegretProcess,
        source, episodes] using h

/-- Expected absolute natural-causal regret is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds := by
  unfold selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret
  dsimp only
  exact integral_nonneg fun _ => abs_nonneg _

/--
The expected absolute natural-causal regret is controlled by the good-event
planning envelope, the bounded model-tail overflow, and the directly integrated
global-return MGF contribution.
-/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret_le_burninL1Envelope
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
    (burnin rounds : Nat) (hburnin : burnin <= rounds)
    (hrounds : 0 < rounds) :
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds <=
      selfConsistentScheduledCausalBurninExpectedAbsoluteRegretL1Envelope mdp
        varianceProxy baseVisitFloor burnin rounds := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, selfConsistentScheduledCausalSource]
    infer_instance
  let mu := source.trajectoryMeasure
  let expectedEnvelope :=
    selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
      varianceProxy baseVisitFloor burnin rounds
  let modelTail := selfConsistentScheduledCausalTailModelFailureBudget mdp burnin
  let returnEnvelope :=
    selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
      varianceProxy baseVisitFloor rounds
  let process := selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor rounds
  let deviation := source.cumulativeSuccessorGlobalReturnDeviation rounds
  let mass := HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
    episodes rounds
  let bad := selfConsistentScheduledCausalTailModelBadEvent mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor burnin
  let overflow : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes ->
      Real := bad.indicator (fun _ => 2 * (mdp.horizon : Real))
  have hepisodes : forall t, 0 < episodes t := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor t
  have hmass : 0 < mass := by
    exact HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_pos
      episodes rounds hrounds hepisodes
  have hexpectedEnvelope : 0 <= expectedEnvelope := by
    exact selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope_nonneg
      mdp varianceProxy baseVisitFloor burnin rounds
  have hbad : MeasurableSet bad := by
    exact measurableSet_selfConsistentScheduledCausalTailModelBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor burnin
  have hprocess : Integrable process mu := by
    simpa [process, mu, source] using
      integrable_selfConsistentScheduledNaturalCausalRealizedRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable
          defaultState baseVisitFloor hrewardBound rounds
  have hmgf : HasSubgaussianMGF deviation
      (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp episodes rounds 1 varianceProxy) mu := by
    simpa [deviation, mu, source] using
      (source.trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_hasSubgaussianMGF
        rounds 1 varianceProxy hrewardBound (by
          simpa [source, selfConsistentScheduledCausalSource] using law))
  have hdeviation : Integrable deviation mu := hmgf.integrable
  have hoverflow : Integrable overflow mu :=
    (integrable_const (2 * (mdp.horizon : Real))).indicator hbad
  have hpoint : forall trajectory,
      |process trajectory| <=
        expectedEnvelope + overflow trajectory +
          |deviation trajectory| / mass := by
    intro trajectory
    have hexpected :
        source.successorWeightedExpectedAverageRegret trajectory rounds <=
          expectedEnvelope + overflow trajectory := by
      by_cases htrajectory : trajectory ∈ bad
      · have hglobal :=
          source.successorWeightedExpectedAverageRegret_le_two_mul_horizon
            trajectory rounds (by simpa [mass] using hmass) hrewardBound
        calc
          source.successorWeightedExpectedAverageRegret trajectory rounds <=
              2 * (mdp.horizon : Real) := hglobal
          _ <= expectedEnvelope + 2 * (mdp.horizon : Real) :=
            le_add_of_nonneg_left hexpectedEnvelope
          _ = expectedEnvelope + overflow trajectory := by
            simp [overflow, Set.indicator_of_mem htrajectory]
      · have hgood :=
          selfConsistentScheduledCausalSource_weightedExpectedSuccessorAverageRegret_le_burninEnvelope
            mdp initialState rewardSource varianceProxy hvarianceProxy law
              initialTable defaultState support baseVisitFloor hbaseFloor
                hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
                  hrounds trajectory (by simpa [bad] using htrajectory)
        calc
          source.successorWeightedExpectedAverageRegret trajectory rounds <=
              expectedEnvelope := by
            simpa [source, expectedEnvelope] using hgood
          _ = expectedEnvelope + overflow trajectory := by
            simp [overflow, Set.indicator_of_notMem htrajectory]
    have habs :=
      source.abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
        trajectory rounds (by simpa [mass] using hmass)
        (expectedEnvelope + overflow trajectory) |deviation trajectory|
        hexpected le_rfl
    simpa [process, deviation, mass,
      selfConsistentScheduledNaturalCausalRealizedRegretProcess, source] using
      habs
  have hdom : Integrable
      (fun trajectory => expectedEnvelope + overflow trajectory +
        |deviation trajectory| / mass) mu :=
    ((integrable_const expectedEnvelope).add hoverflow).add
      (hdeviation.abs.div_const mass)
  have hoverflowIntegral : integral mu overflow =
      (2 * (mdp.horizon : Real)) * mu.real bad := by
    change integral mu (bad.indicator
        (fun _trajectory => 2 * (mdp.horizon : Real))) =
      (2 * (mdp.horizon : Real)) * mu.real bad
    rw [integral_indicator hbad, setIntegral_const]
    simp [Measure.real, smul_eq_mul, mul_comm]
  have htail :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_tailModelBadEvent_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState baseVisitFloor burnin
  have htailReal : mu.real bad <= modelTail.toReal := by
    rw [Measure.real]
    exact ENNReal.toReal_mono
      (selfConsistentScheduledCausalTailModelFailureBudget_ne_top mdp burnin)
      (by simpa [mu, source, bad, modelTail] using htail)
  have hdeviationIntegral :
      integral mu (fun trajectory => |deviation trajectory|) <=
        2 * Real.sqrt
          (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp episodes rounds 1 varianceProxy : Real) *
          Real.exp (1 / 2 : Real) := by
    exact
      Concentration.integral_abs_le_two_mul_sqrt_mul_exp_half_of_hasSubgaussianMGF
        mu deviation
          (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp episodes rounds 1 varianceProxy) hmgf
  change integral mu (fun trajectory => |process trajectory|) <=
    expectedEnvelope +
      2 * (mdp.horizon : Real) * modelTail.toReal + returnEnvelope
  calc
    integral mu (fun trajectory => |process trajectory|) <=
        integral mu (fun trajectory => expectedEnvelope + overflow trajectory +
          |deviation trajectory| / mass) :=
      integral_mono hprocess.abs hdom hpoint
    _ = expectedEnvelope +
          (2 * (mdp.horizon : Real)) * mu.real bad +
          integral mu (fun trajectory => |deviation trajectory|) / mass := by
      calc
        integral mu (fun trajectory => expectedEnvelope + overflow trajectory +
            |deviation trajectory| / mass) =
            integral mu (fun trajectory => expectedEnvelope + overflow trajectory) +
              integral mu (fun trajectory => |deviation trajectory| / mass) := by
          exact integral_add ((integrable_const expectedEnvelope).add hoverflow)
            (hdeviation.abs.div_const mass)
        _ = (integral mu (fun _trajectory => expectedEnvelope) +
              integral mu overflow) +
              integral mu (fun trajectory => |deviation trajectory|) / mass := by
          rw [integral_add (integrable_const expectedEnvelope) hoverflow,
            integral_div]
        _ = expectedEnvelope +
              (2 * (mdp.horizon : Real)) * mu.real bad +
              integral mu (fun trajectory => |deviation trajectory|) / mass := by
          rw [integral_const, hoverflowIntegral]
          simp [MeasureTheory.probReal_univ]
    _ <= expectedEnvelope +
          2 * (mdp.horizon : Real) * modelTail.toReal +
          (2 * Real.sqrt
            (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp episodes rounds 1 varianceProxy : Real) *
            Real.exp (1 / 2 : Real)) / mass := by
      exact add_le_add
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left htailReal (by positivity)))
        (div_le_div_of_nonneg_right hdeviationIntegral hmass.le)
    _ = expectedEnvelope +
          2 * (mdp.horizon : Real) * modelTail.toReal + returnEnvelope := by
      rfl

/-- Expected absolute regret on the natural causal prefixes tends to zero. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret_tendsto_zero
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
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) := by
  have hfailure : Tendsto
      (fun burnin => 2 * (mdp.horizon : Real) *
        (selfConsistentScheduledCausalTailModelFailureBudget mdp burnin).toReal)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _burnin : Nat => 2 * (mdp.horizon : Real))
        atTop (nhds (2 * (mdp.horizon : Real))) := tendsto_const_nhds
    simpa using hconst.mul
      (selfConsistentScheduledCausalTailModelFailureBudget_toReal_tendsto_zero mdp)
  rw [Metric.tendsto_atTop] at hfailure ⊢
  intro epsilon hepsilon
  obtain ⟨burnin, hburnin⟩ := hfailure (epsilon / 2) (by linarith)
  have hfixed : Tendsto
      (fun rounds =>
        selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
            varianceProxy baseVisitFloor burnin rounds +
          selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
            varianceProxy baseVisitFloor rounds) atTop (nhds 0) := by
    simpa using
      (selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope_tendsto_zero
        mdp varianceProxy baseVisitFloor burnin).add
        (selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound_tendsto_zero
          mdp varianceProxy baseVisitFloor)
  rw [Metric.tendsto_atTop] at hfixed
  obtain ⟨N, hN⟩ := hfixed (epsilon / 2) (by linarith)
  refine ⟨max 1 (max burnin N), ?_⟩
  intro rounds hroundsN
  have hrounds : 0 < rounds :=
    lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (le_max_left 1 (max burnin N)) hroundsN)
  have hburninRounds : burnin <= rounds :=
    le_trans (le_trans (le_max_left burnin N)
      (le_max_right 1 (max burnin N))) hroundsN
  have hNrounds : N <= rounds :=
    le_trans (le_trans (le_max_right burnin N)
      (le_max_right 1 (max burnin N))) hroundsN
  have hfailureNonneg : 0 <= 2 * (mdp.horizon : Real) *
      (selfConsistentScheduledCausalTailModelFailureBudget mdp burnin).toReal :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hfailureSmall : 2 * (mdp.horizon : Real) *
      (selfConsistentScheduledCausalTailModelFailureBudget mdp burnin).toReal <
        epsilon / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg hfailureNonneg] using
      hburnin burnin le_rfl
  have hfixedNonneg : 0 <=
      selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
          varianceProxy baseVisitFloor burnin rounds +
        selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
          varianceProxy baseVisitFloor rounds :=
    add_nonneg
      (selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope_nonneg
        mdp varianceProxy baseVisitFloor burnin rounds)
      (selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound_nonneg
        mdp varianceProxy baseVisitFloor rounds)
  have hfixedSmall :
      selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
          varianceProxy baseVisitFloor burnin rounds +
        selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
          varianceProxy baseVisitFloor rounds < epsilon / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg hfixedNonneg] using hN rounds hNrounds
  have hexpectedNonneg :=
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hexpectedNonneg]
  calc
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds <=
        selfConsistentScheduledCausalBurninExpectedAbsoluteRegretL1Envelope mdp
          varianceProxy baseVisitFloor burnin rounds :=
      selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret_le_burninL1Envelope
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor burnin rounds hburninRounds
              hrounds
    _ = (selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
            varianceProxy baseVisitFloor burnin rounds +
          selfConsistentScheduledCausalNormalizedReturnMGFFirstMomentBound mdp
            varianceProxy baseVisitFloor rounds) +
        2 * (mdp.horizon : Real) *
          (selfConsistentScheduledCausalTailModelFailureBudget mdp burnin).toReal := by
      unfold selfConsistentScheduledCausalBurninExpectedAbsoluteRegretL1Envelope
      ring
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hfixedSmall hfailureSmall
    _ = epsilon := by ring

/-- Every coordinate of the natural causal process belongs to `L1`. -/
theorem memLp_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    MemLp
      (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  rw [memLp_one_iff_integrable]
  exact integrable_selfConsistentScheduledNaturalCausalRealizedRegretProcess
    mdp initialState rewardSource varianceProxy law initialTable defaultState
      baseVisitFloor hrewardBound rounds

/-- At exponent one, `eLpNorm` is the lifted expected absolute regret. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    eLpNorm
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds)]
  simp [selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret,
    Real.norm_eq_abs]

/-- The exponent-one extended norm on the causal prefixes tends to zero. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_tendsto_zero
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
    Tendsto
      (fun rounds => eLpNorm
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have hexpected :=
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hexpected
  simpa only [ENNReal.ofReal_zero,
    eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_eq
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound] using hofReal

/-- Canonical natural-causal `L1` norm-of-the-difference convergence. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_sub_zero_tendsto_zero
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
    Tendsto
      (fun rounds => eLpNorm
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds -
          (fun _ => 0))
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have h :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  convert h using 1
  funext rounds
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-- The natural causal realized-regret process as an `Lp Real 1` value. -/
noncomputable def selfConsistentScheduledNaturalCausalRealizedRegretLp
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    Lp Real 1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure :=
  (memLp_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess
    mdp initialState rewardSource varianceProxy law initialTable defaultState
      baseVisitFloor hrewardBound rounds).toLp
    (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor rounds)

/-- The named natural-causal `Lp` coordinate represents the process a.e. -/
theorem selfConsistentScheduledNaturalCausalRealizedRegretLp_coeFn_ae_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    (selfConsistentScheduledNaturalCausalRealizedRegretLp mdp initialState
        rewardSource varianceProxy law initialTable defaultState baseVisitFloor
          hrewardBound rounds :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real) =ᵐ[
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure]
      selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          rounds := by
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds).coeFn_toLp

/-- The named natural-causal `Lp Real 1` process converges to zero. -/
theorem selfConsistentScheduledNaturalCausalRealizedRegretLp_tendsto_zero
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
    Tendsto
      (selfConsistentScheduledNaturalCausalRealizedRegretLp mdp initialState
        rewardSource varianceProxy law initialTable defaultState baseVisitFloor
          hrewardBound)
      atTop (nhds 0) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let process := fun rounds =>
    selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor rounds
  have hmem : forall rounds, MemLp (process rounds) 1 source.trajectoryMeasure :=
    fun rounds =>
      memLp_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds
  have hzero : MemLp
      (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) => (0 : Real))
      1 source.trajectoryMeasure := MemLp.zero'
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hLp :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' process hmem (fun _ => (0 : Real))
      hzero).2 (by simpa [process, source] using hnorm)
  simpa [selfConsistentScheduledNaturalCausalRealizedRegretLp, process, source]
    using hLp

/--
Terminal natural-causal `L1` theorem on one heterogeneous dependent trajectory
measure: exact exponent-one norms, `Lp` convergence, and convergence in measure.
-/
theorem selfConsistentScheduledCausalSource_naturalRealizedRegret_memLp_eLpNorm_L1_tendsto_zero
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
    (forall rounds, MemLp
      (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      1 source.trajectoryMeasure) /\
    (forall rounds, eLpNorm
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)
        1 source.trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteRealizedRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)) /\
    Tendsto
      (fun rounds => eLpNorm
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds -
          (fun _ => 0))
        1 source.trajectoryMeasure)
      atTop (nhds 0) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalRealizedRegretLp mdp initialState
        rewardSource varianceProxy law initialTable defaultState baseVisitFloor
          hrewardBound)
      atTop (nhds 0) /\
    TendstoInMeasure source.trajectoryMeasure
      (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (fun _ => 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hmem := fun rounds =>
    memLp_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  refine ⟨hmem, fun rounds =>
    eLpNorm_one_selfConsistentScheduledNaturalCausalRealizedRegretProcess_eq
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds,
    hnorm,
    selfConsistentScheduledNaturalCausalRealizedRegretLp_tendsto_zero mdp
      initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    ?_⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun rounds => (hmem rounds).aestronglyMeasurable)
    (by fun_prop) hnorm

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
