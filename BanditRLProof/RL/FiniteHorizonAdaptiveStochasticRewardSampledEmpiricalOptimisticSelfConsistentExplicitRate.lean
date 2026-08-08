import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentSchedule

/-!
# Explicit finite-window rate for sampled self-consistent optimism

This consumer keeps the scheduled source and all its regularity contracts
unchanged.  It combines the compiled bounds

* `rewardBudget < scale^-2`,
* `q < 4 * card State * horizon / scale^2`, and
* `q <= 1 / 2`

to expose closed finite-window failure and realized-regret envelopes.  The
proof route uses only the local self-consistent schedule, the explicit
exploration charge, the normalized return-radius envelope, and ordered-field
algebra (`MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`, and
`MLIB-ASYMPTOTICS`).  No theorem-card or proof-weapon statement is used as a
Lean proof.

Failure policy: preserve actual sampled rewards, three separate confidence
shares, global return centering, and changing finite-window sample spaces.  A
failure here must remain a rate-algebra or local-API issue; it must not be
repaired by weakening the source law, replacing sampled rewards by means, or
claiming a common process, anytime control, minimax regret, or complete UCB-VI.
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

namespace AdaptiveStochasticEpisodeBatchSource

/-- Three times the compiled contraction envelope controls the fixed-point budget. -/
noncomputable def selfConsistentScheduledTransitionBudgetRateEnvelope
    (mdp : MDP State Action) (n : Nat) : Real :=
  3 * selfConsistentScheduledTransitionContractionEnvelope mdp n

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit transition-budget envelope is `12 * |State| * horizon / scale^2`. -/
theorem selfConsistentScheduledTransitionBudgetRateEnvelope_eq
    (mdp : MDP State Action) (n : Nat) :
    selfConsistentScheduledTransitionBudgetRateEnvelope mdp n =
      (12 * (Fintype.card State : Real) * (mdp.horizon : Real)) /
        (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2 := by
  unfold selfConsistentScheduledTransitionBudgetRateEnvelope
    selfConsistentScheduledTransitionContractionEnvelope
  ring

/-- The exact fixed-point transition budget has an explicit scale-squared rate. -/
theorem selfConsistentScheduledTransitionBudget_le_rateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    selfConsistentScheduledTransitionBudget mdp varianceProxy baseVisitFloor n <=
      selfConsistentScheduledTransitionBudgetRateEnvelope mdp n := by
  let witnessState : State := Classical.choice inferInstance
  let scale : Real := AdaptiveEpisodeBatchSource.decayingExplorationScale n
  let rewardBudget :=
    selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor n
  let contraction :=
    selfConsistentScheduledTransitionContraction mdp varianceProxy
      baseVisitFloor n
  let contractionEnvelope :=
    selfConsistentScheduledTransitionContractionEnvelope mdp n
  have hscalePos : 0 < scale := by
    dsimp [scale]
    exact_mod_cast AdaptiveEpisodeBatchSource.decayingExplorationScale_pos n
  have hscaleFour : 4 <= scale ^ 2 := by
    have hscaleTwo : 2 <= scale := by
      simp [scale, AdaptiveEpisodeBatchSource.decayingExplorationScale]
    nlinarith
  have hinvQuarter : 1 / scale ^ 2 <= (1 : Real) / 4 :=
    one_div_le_one_div_of_le (by norm_num) hscaleFour
  have hrewardNonneg : 0 <= rewardBudget := by
    dsimp [rewardBudget]
    exact selfConsistentScheduledRewardBudget_nonneg mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n
  have hrewardScale : rewardBudget <= 1 / scale ^ 2 := by
    dsimp [rewardBudget, scale]
    exact (selfConsistentScheduledRewardBudget_lt_inv_scale_sq mdp
      varianceProxy hhorizon hbaseVisitFloor n).le
  have hrewardQuarter : rewardBudget <= (1 : Real) / 4 :=
    hrewardScale.trans hinvQuarter
  have hcontractionNonneg : 0 <= contraction := by
    dsimp [contraction]
    exact selfConsistentScheduledTransitionContraction_nonneg mdp witnessState
      varianceProxy hhorizon hbaseVisitFloor n
  have hcontractionHalf : contraction <= (1 : Real) / 2 := by
    have hhalf :=
      (selfConsistentScheduled_countMargin_and_halfContraction mdp witnessState
        varianceProxy hhorizon hbaseVisitFloor n).2
    simpa [contraction, selfConsistentScheduledTransitionContraction] using hhalf
  have hcontractionEnvelope : contraction <= contractionEnvelope := by
    dsimp [contraction, contractionEnvelope]
    exact (selfConsistentScheduledTransitionContraction_lt_envelope mdp
      varianceProxy hhorizon hbaseVisitFloor n).le
  have hdenominatorPos : 0 < 1 - contraction := by linarith
  have hrewardProduct :
      0 <= contraction * ((1 : Real) / 4 - rewardBudget) :=
    mul_nonneg hcontractionNonneg (sub_nonneg.mpr hrewardQuarter)
  have hcontractionProduct :
      0 <= contraction * ((1 : Real) / 2 - contraction) :=
    mul_nonneg hcontractionNonneg (sub_nonneg.mpr hcontractionHalf)
  have hfixedPoint :
      contraction * (1 + 2 * rewardBudget) / (1 - contraction) <=
        3 * contraction := by
    rw [div_le_iff₀ hdenominatorPos]
    nlinarith
  change contraction * (1 + 2 * rewardBudget) / (1 - contraction) <=
    3 * contractionEnvelope
  exact hfixedPoint.trans
    (mul_le_mul_of_nonneg_left hcontractionEnvelope (by norm_num))

/-- Explicit planning envelope: scale-squared model error plus the exploration charge. -/
noncomputable def selfConsistentScheduledPlanningAverageRegretRateEnvelope
    (mdp : MDP State Action) (n : Nat) : Real :=
  (mdp.horizon : Real) *
      (2 *
        (1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2 +
          selfConsistentScheduledTransitionBudgetRateEnvelope mdp n)) +
    exploratoryBehaviorRegretCharge mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationRate n) 1

/-- The scheduled planning certificate is bounded by the explicit rate envelope. -/
theorem selfConsistentScheduledPlanningAverageRegretBound_le_rateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    selfConsistentScheduledPlanningAverageRegretBound mdp varianceProxy
        baseVisitFloor n <=
      selfConsistentScheduledPlanningAverageRegretRateEnvelope mdp n := by
  let rewardBudget :=
    selfConsistentScheduledRewardBudget mdp varianceProxy baseVisitFloor n
  let transitionBudget :=
    selfConsistentScheduledTransitionBudget mdp varianceProxy baseVisitFloor n
  have hreward : rewardBudget <=
      1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2 := by
    dsimp [rewardBudget]
    exact (selfConsistentScheduledRewardBudget_lt_inv_scale_sq mdp
      varianceProxy hhorizon hbaseVisitFloor n).le
  have htransition : transitionBudget <=
      selfConsistentScheduledTransitionBudgetRateEnvelope mdp n := by
    dsimp [transitionBudget]
    exact selfConsistentScheduledTransitionBudget_le_rateEnvelope mdp
      varianceProxy hhorizon hbaseVisitFloor n
  have hsum := add_le_add hreward htransition
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : Real) <= 2))
    (by positivity : (0 : Real) <= (mdp.horizon : Real))
  unfold selfConsistentScheduledPlanningAverageRegretBound
    adaptiveStochasticSampledEmpiricalOptimisticSelfConsistentBudgetAverageBound
    selfConsistentScheduledPlanningAverageRegretRateEnvelope
  change (mdp.horizon : Real) * (2 * (rewardBudget + transitionBudget)) +
      exploratoryBehaviorRegretCharge mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationRate n) 1 <= _
  exact add_le_add hscaled (le_refl _)

/-- Closed full realized-rate envelope, including the global return fluctuation. -/
noncomputable def selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) (n : Nat) : Real :=
  selfConsistentScheduledPlanningAverageRegretRateEnvelope mdp n +
    decayingExplorationStochasticReturnRadiusEnvelope mdp 1 varianceProxy n

/-- The original realized-regret certificate is bounded by the closed rate envelope. -/
theorem selfConsistentScheduledRealizedSuccessorAverageRegretBound_le_rateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    selfConsistentScheduledRealizedSuccessorAverageRegretBound mdp varianceProxy
        baseVisitFloor n <=
      selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope mdp
        varianceProxy n := by
  unfold selfConsistentScheduledRealizedSuccessorAverageRegretBound
    selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
  exact add_le_add
    (selfConsistentScheduledPlanningAverageRegretBound_le_rateEnvelope mdp
      varianceProxy hhorizon hbaseVisitFloor n)
    (normalizedSuccessorGlobalReturnConfidenceRadius_le_decayingEnvelope mdp
      (selfConsistentScheduledEpisodes mdp varianceProxy baseVisitFloor n)
      1 varianceProxy n
      (selfConsistentScheduledEpisodes_pos mdp varianceProxy baseVisitFloor n))

/-- The three confidence shares equal the explicit `3 / (n + 2)` envelope. -/
noncomputable def selfConsistentScheduledRealizedFailureRateEnvelope
    (n : Nat) : ENNReal :=
  ENNReal.ofReal
    (3 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real))

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The old three-share budget is exactly the explicit failure-rate envelope. -/
theorem selfConsistentScheduledRealizedFailureBudget_eq_rateEnvelope (n : Nat) :
    selfConsistentScheduledRealizedFailureBudget n =
      selfConsistentScheduledRealizedFailureRateEnvelope n := by
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  have hdelta : 0 <= delta :=
    (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n).le
  unfold selfConsistentScheduledRealizedFailureBudget
    selfConsistentScheduledRealizedFailureRateEnvelope
  rw [← ENNReal.ofReal_add hdelta hdelta]
  rw [← ENNReal.ofReal_add (add_nonneg hdelta hdelta) hdelta]
  congr 1
  dsimp [delta, AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta,
    AdaptiveEpisodeBatchSource.decayingExplorationScale]
  ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit planning-rate envelope tends to zero. -/
theorem selfConsistentScheduledPlanningAverageRegretRateEnvelope_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto (selfConsistentScheduledPlanningAverageRegretRateEnvelope mdp)
      atTop (nhds 0) := by
  have hinvSq : Tendsto
      (fun n : Nat =>
        1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop decayingExplorationScale_sq_tendsto_atTop
  have htransition : Tendsto
      (selfConsistentScheduledTransitionBudgetRateEnvelope mdp)
      atTop (nhds 0) := by
    unfold selfConsistentScheduledTransitionBudgetRateEnvelope
    simpa using tendsto_const_nhds.mul
      (selfConsistentScheduledTransitionContractionEnvelope_tendsto_zero mdp)
  have hmodel : Tendsto
      (fun n : Nat => (mdp.horizon : Real) *
        (2 *
          (1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2 +
            selfConsistentScheduledTransitionBudgetRateEnvelope mdp n)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_const_nhds.mul (hinvSq.add htransition))
  unfold selfConsistentScheduledPlanningAverageRegretRateEnvelope
  simpa using hmodel.add
    (AdaptiveEpisodeBatchSource.decayingExplorationBehaviorCharge_tendsto_zero mdp)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The full explicit realized-regret envelope tends to zero. -/
theorem selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope mdp
        varianceProxy)
      atTop (nhds 0) := by
  unfold selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
  simpa using
    (selfConsistentScheduledPlanningAverageRegretRateEnvelope_tendsto_zero mdp).add
      (decayingExplorationStochasticReturnRadiusEnvelope_tendsto_zero
        mdp 1 varianceProxy)

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit `3 / (n + 2)` failure envelope tends to zero. -/
theorem selfConsistentScheduledRealizedFailureRateEnvelope_tendsto_zero :
    Tendsto selfConsistentScheduledRealizedFailureRateEnvelope atTop (nhds 0) := by
  have heq : selfConsistentScheduledRealizedFailureRateEnvelope =
      selfConsistentScheduledRealizedFailureBudget := by
    funext n
    exact (selfConsistentScheduledRealizedFailureBudget_eq_rateEnvelope n).symm
  rw [heq]
  exact selfConsistentScheduledRealizedFailureBudget_tendsto_zero

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Explicit failure and realized-regret rates vanish jointly. -/
theorem selfConsistentScheduledExplicitRateEnvelopes_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (fun n =>
        (selfConsistentScheduledRealizedFailureRateEnvelope n,
          selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope mdp
            varianceProxy n))
      atTop (nhds (0, 0)) := by
  rw [nhds_prod_eq]
  exact selfConsistentScheduledRealizedFailureRateEnvelope_tendsto_zero.prodMk
    (selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope_tendsto_zero
      mdp varianceProxy)

end AdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-!
The terminal below changes only the numerical certificate exposed by the
compiled scheduled theorem.  Its source, events, optimism assertion, and
changing-window semantics are definitionally the same.
-/

/-- Actual-sampled optimism and realized regret with explicit finite-window rates. -/
theorem exploratorySource_trajectoryMeasure_selfConsistentScheduledExplicitRate_allCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret
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
    let episodes :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor n
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
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureRateEnvelope n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
              defaultState rewardBudget transitionBudget round).upperValueRemaining
                mdp.horizon le_rfl state) /\
          source.realizedSuccessorAverageRegret trajectory rounds <=
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
              mdp varianceProxy n := by
  dsimp only
  have hparent :=
    exploratorySource_trajectoryMeasure_selfConsistentScheduled_allCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret
      mdp initialState baseVisitFloor n rewardSource varianceProxy hvarianceProxy
      law initialTable defaultState support hbaseFloor hrewardBound hhorizon
      hbaseVisitFloor
  dsimp only at hparent
  refine ⟨hparent.1, ?_, ?_⟩
  · exact hparent.2.1.trans_eq
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureBudget_eq_rateEnvelope n)
  · intro trajectory htrajectory
    have hgood := hparent.2.2 trajectory htrajectory
    exact ⟨hgood.1, hgood.2.trans
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretBound_le_rateEnvelope
        mdp varianceProxy hhorizon hbaseVisitFloor n)⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
