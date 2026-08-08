import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeExploratoryBehaviorRegret

/-!
# Decaying-exploration high-probability behavior consistency

This module closes the fixed-exploration residual charge in the exploratory
behavior-regret route.  It starts from one path-support visit floor at full
exploration, proves the exact stagewise power scaling at a smaller exploration
rate, and chooses

* `explorationRate_n = 1 / (n + 2)`,
* `rounds_n = (n + 2) ^ (horizon + 4)`, and
* `visitFloor_n = baseVisitFloor * explorationRate_n ^ horizon`.

The effective visit mass is therefore `baseVisitFloor * (n + 2) ^ 4`.
The scheduled recommendation certificate is `O((n + 2) ^ -2)`, while the
behavior exploration charge is `O((n + 2) ^ -1)`.  Both the confidence budget
and the resulting deterministic average exploratory-behavior expected-regret
certificate tend to zero.

Each finite window still has its own episode count and trajectory type.  The
source theorem is consequently a family of finite-window outer-measure
certificates, not a pathwise, almost-sure, realized-regret, or common-process
convergence theorem.
-/

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory Topology

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

omit [MeasurableSpace State] [MeasurableSpace Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem exploratoryActionProbabilityFloor_eq_rate_mul_one
    (explorationRate : NNReal) :
    exploratoryActionProbabilityFloor Action explorationRate =
      (explorationRate : Real) * exploratoryActionProbabilityFloor Action 1 := by
  simp [exploratoryActionProbabilityFloor]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem exploratoryPathStateLowerNat_eq_rate_pow_mul_one
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) :
    forall (stage : Nat) (hstage : stage < mdp.horizon) (state : State),
      exploratoryPathStateLowerNat support explorationRate stage hstage state =
        (explorationRate : Real) ^ stage *
          exploratoryPathStateLowerNat support 1 stage hstage state := by
  intro stage
  induction stage with
  | zero =>
      intro hstage state
      simp [exploratoryPathStateLowerNat]
  | succ stage ih =>
      intro hstage state
      rw [exploratoryPathStateLowerNat, exploratoryPathStateLowerNat]
      rw [ih]
      rw [exploratoryActionProbabilityFloor_eq_rate_mul_one]
      rw [pow_succ]
      ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem exploratoryPathVisitLower_eq_rate_pow_mul_one
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) (stage : Fin mdp.horizon) (state : State) :
    exploratoryPathStateLower support explorationRate stage state *
        exploratoryActionProbabilityFloor Action explorationRate =
      (explorationRate : Real) ^ (stage.val + 1) *
        (exploratoryPathStateLower support 1 stage state *
          exploratoryActionProbabilityFloor Action 1) := by
  unfold exploratoryPathStateLower
  rw [exploratoryPathStateLowerNat_eq_rate_pow_mul_one]
  rw [exploratoryActionProbabilityFloor_eq_rate_mul_one]
  rw [pow_succ]
  ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem ExploratoryPathUniformVisitFloor.scale_explorationRate
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    {baseVisitFloor : Real}
    (hfloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    ExploratoryPathUniformVisitFloor support explorationRate
      (baseVisitFloor * (explorationRate : Real) ^ mdp.horizon) := by
  intro stage state
  have hpow :
      (explorationRate : Real) ^ mdp.horizon <=
        (explorationRate : Real) ^ (stage.val + 1) := by
    exact pow_le_pow_of_le_one (NNReal.coe_nonneg explorationRate)
      (by exact_mod_cast hexplorationRate) (by omega)
  have honeNonneg :
      0 <= exploratoryPathStateLower support 1 stage state *
        exploratoryActionProbabilityFloor Action 1 :=
    mul_nonneg (exploratoryPathStateLower_nonneg support 1 stage state)
      (exploratoryActionProbabilityFloor_nonneg 1)
  calc
    baseVisitFloor * (explorationRate : Real) ^ mdp.horizon <=
        (exploratoryPathStateLower support 1 stage state *
            exploratoryActionProbabilityFloor Action 1) *
          (explorationRate : Real) ^ mdp.horizon :=
      mul_le_mul_of_nonneg_right (hfloor stage state) (by positivity)
    _ <= (exploratoryPathStateLower support 1 stage state *
            exploratoryActionProbabilityFloor Action 1) *
          (explorationRate : Real) ^ (stage.val + 1) :=
      mul_le_mul_of_nonneg_left hpow honeNonneg
    _ = (explorationRate : Real) ^ (stage.val + 1) *
          (exploratoryPathStateLower support 1 stage state *
            exploratoryActionProbabilityFloor Action 1) := by ring
    _ = exploratoryPathStateLower support explorationRate stage state *
          exploratoryActionProbabilityFloor Action explorationRate :=
      (exploratoryPathVisitLower_eq_rate_pow_mul_one
        support explorationRate stage state).symm

namespace AdaptiveEpisodeBatchSource

def decayingExplorationScale (n : Nat) : Nat := n + 2

noncomputable def decayingExplorationRate (n : Nat) : NNReal :=
  (decayingExplorationScale n : NNReal)⁻¹

def decayingExplorationRounds (mdp : MDP State Action) (n : Nat) : Nat :=
  decayingExplorationScale n ^ (mdp.horizon + 4)

noncomputable def decayingExplorationVisitFloor
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Real :=
  baseVisitFloor * (decayingExplorationRate n : Real) ^ mdp.horizon

noncomputable def decayingExplorationScheduledEpisodes
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Nat :=
  normalizedCumulativeInverseSqrtScheduledEpisodes mdp
    (decayingExplorationRounds mdp n) (vanishingAverageConfidenceDelta n)
    (decayingExplorationVisitFloor mdp baseVisitFloor n)

noncomputable def decayingExplorationAverageRecommendedExpectedRegretBound
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Real :=
  normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound mdp
    (decayingExplorationScheduledEpisodes mdp baseVisitFloor n)
    (decayingExplorationRounds mdp n) (vanishingAverageConfidenceDelta n)
    (decayingExplorationVisitFloor mdp baseVisitFloor n)

noncomputable def decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Real :=
  decayingExplorationAverageRecommendedExpectedRegretBound mdp baseVisitFloor n +
    exploratoryBehaviorRegretCharge mdp (decayingExplorationRate n) 1

noncomputable def decayingExplorationAverageEnvelope
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Real :=
  16 * (Fintype.card State : Real) * (mdp.horizon : Real) ^ 2 /
      Real.sqrt baseVisitFloor /
    (decayingExplorationScale n : Real) ^ 2

omit [MeasurableSpace State] [MeasurableSpace Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationScale_pos (n : Nat) :
    0 < decayingExplorationScale n := by
  simp [decayingExplorationScale]

omit [MeasurableSpace State] [MeasurableSpace Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationRate_pos (n : Nat) :
    0 < decayingExplorationRate n := by
  simp [decayingExplorationRate, decayingExplorationScale]

omit [MeasurableSpace State] [MeasurableSpace Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationRate_le_one (n : Nat) :
    decayingExplorationRate n <= 1 := by
  rw [decayingExplorationRate]
  exact inv_le_one_of_one_le₀ (by
    exact_mod_cast (show 1 <= decayingExplorationScale n by
      simp [decayingExplorationScale]))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationRounds_pos
    (mdp : MDP State Action) (n : Nat) :
    0 < decayingExplorationRounds mdp n := by
  exact pow_pos (decayingExplorationScale_pos n) _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationVisitFloor_pos
    (mdp : MDP State Action) {baseVisitFloor : Real}
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    0 < decayingExplorationVisitFloor mdp baseVisitFloor n := by
  unfold decayingExplorationVisitFloor
  exact mul_pos hbaseVisitFloor
    (pow_pos (by exact_mod_cast decayingExplorationRate_pos n) _)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationVisitFloor_mul_rounds
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) :
    decayingExplorationVisitFloor mdp baseVisitFloor n *
        (decayingExplorationRounds mdp n : Real) =
      baseVisitFloor * (decayingExplorationScale n : Real) ^ 4 := by
  have hscalePos : 0 < (decayingExplorationScale n : Real) := by
    exact_mod_cast decayingExplorationScale_pos n
  have hscale : (decayingExplorationScale n : Real) ≠ 0 := ne_of_gt hscalePos
  unfold decayingExplorationVisitFloor decayingExplorationRate
    decayingExplorationRounds
  push_cast
  rw [pow_add]
  have hcancel :
      (decayingExplorationScale n : Real)⁻¹ ^ mdp.horizon *
          (decayingExplorationScale n : Real) ^ mdp.horizon = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hscale, one_pow]
  calc
    baseVisitFloor * (decayingExplorationScale n : Real)⁻¹ ^ mdp.horizon *
          ((decayingExplorationScale n : Real) ^ mdp.horizon *
            (decayingExplorationScale n : Real) ^ 4) =
        baseVisitFloor *
            ((decayingExplorationScale n : Real)⁻¹ ^ mdp.horizon *
              (decayingExplorationScale n : Real) ^ mdp.horizon) *
          (decayingExplorationScale n : Real) ^ 4 := by ring
    _ = baseVisitFloor * (decayingExplorationScale n : Real) ^ 4 := by
      rw [hcancel]
      ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationUniformVisitFloor
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    {baseVisitFloor : Real}
    (hfloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (n : Nat) :
    ExploratoryPathUniformVisitFloor support (decayingExplorationRate n)
      (decayingExplorationVisitFloor mdp baseVisitFloor n) := by
  exact hfloor.scale_explorationRate support (decayingExplorationRate n)
    (decayingExplorationRate_le_one n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem normalizedScheduledAverageEnvelope_decayingExploration_eq
    (mdp : MDP State Action) {baseVisitFloor : Real}
    (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    normalizedCumulativeInverseSqrtScheduledAverageEnvelope mdp
        (decayingExplorationRounds mdp n)
        (decayingExplorationVisitFloor mdp baseVisitFloor n) =
      decayingExplorationAverageEnvelope mdp baseVisitFloor n := by
  have hvisitFloor :
      0 < decayingExplorationVisitFloor mdp baseVisitFloor n :=
    decayingExplorationVisitFloor_pos mdp hbaseVisitFloor n
  have hscaleNonneg : 0 <= (decayingExplorationScale n : Real) := by
    positivity
  have hsqrtPow :
      Real.sqrt ((decayingExplorationScale n : Real) ^ 4) =
        (decayingExplorationScale n : Real) ^ 2 := by
    rw [show (decayingExplorationScale n : Real) ^ 4 =
        ((decayingExplorationScale n : Real) ^ 2) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold normalizedCumulativeInverseSqrtScheduledAverageEnvelope
    decayingExplorationAverageEnvelope
  rw [div_div]
  rw [← Real.sqrt_mul hvisitFloor.le]
  rw [decayingExplorationVisitFloor_mul_rounds]
  rw [Real.sqrt_mul hbaseVisitFloor.le]
  rw [hsqrtPow]
  rw [div_div]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationAverageEnvelope_tendsto_zero
    (mdp : MDP State Action) (baseVisitFloor : Real) :
    Tendsto
      (fun n => decayingExplorationAverageEnvelope mdp baseVisitFloor n)
      atTop (nhds 0) := by
  have hscale :
      Tendsto (fun n : Nat => (decayingExplorationScale n : Real))
        atTop atTop := by
    change Tendsto (fun n : Nat => (((n + 2 : Nat) : Real))) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hsquare :
      Tendsto (fun n : Nat => (decayingExplorationScale n : Real) ^ 2)
        atTop atTop :=
    (tendsto_pow_atTop (α := Real) (by norm_num : (2 : Nat) ≠ 0)).comp hscale
  simpa [decayingExplorationAverageEnvelope] using
    (tendsto_const_nhds.div_atTop hsquare)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationBehaviorCharge_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto
      (fun n => exploratoryBehaviorRegretCharge mdp (decayingExplorationRate n) 1)
      atTop (nhds 0) := by
  have hscale :
      Tendsto (fun n : Nat => (decayingExplorationScale n : Real))
        atTop atTop := by
    change Tendsto (fun n : Nat => (((n + 2 : Nat) : Real))) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hrate :
      Tendsto (fun n : Nat => (decayingExplorationRate n : Real))
        atTop (nhds 0) := by
    simpa [decayingExplorationRate] using hscale.inv_tendsto_atTop
  unfold exploratoryBehaviorRegretCharge
  simpa only [zero_mul] using
    ((hrate.mul_const 1).mul_const (mdp.horizon : Real)).mul_const
      ((mdp.horizon + 1 : Nat) : Real)

theorem decayingExplorationAverageExploratoryBehaviorBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (fun n =>
        decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
          mdp baseVisitFloor n)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    unfold decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      decayingExplorationAverageRecommendedExpectedRegretBound
      decayingExplorationScheduledEpisodes
    apply add_nonneg
    · exact normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg mdp
        hhorizon (decayingExplorationRounds_pos mdp n)
        (vanishingAverageConfidenceDelta_pos n)
        (vanishingAverageConfidenceDelta_le_one n)
        (decayingExplorationVisitFloor_pos mdp hbaseVisitFloor n)
    · unfold exploratoryBehaviorRegretCharge
      positivity
  · intro n
    unfold decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      decayingExplorationAverageRecommendedExpectedRegretBound
      decayingExplorationScheduledEpisodes
    apply add_le_add
    · exact (normalizedCumulativeInverseSqrtScheduledAverageBound_le_envelope
        mdp hhorizon (decayingExplorationRounds_pos mdp n)
        (vanishingAverageConfidenceDelta_pos n)
        (vanishingAverageConfidenceDelta_le_one n)
        (decayingExplorationVisitFloor_pos mdp hbaseVisitFloor n)).trans_eq
          (normalizedScheduledAverageEnvelope_decayingExploration_eq
            mdp hbaseVisitFloor n)
    · exact le_rfl
  · simpa only [add_zero] using
      (decayingExplorationAverageEnvelope_tendsto_zero mdp baseVisitFloor).add
        (decayingExplorationBehaviorCharge_tendsto_zero mdp)

theorem decayingExplorationDeltaAndAverageExploratoryBehaviorBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (fun n =>
        (ENNReal.ofReal (vanishingAverageConfidenceDelta n),
          decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
            mdp baseVisitFloor n))
      atTop (nhds (0, 0)) := by
  rw [nhds_prod_eq]
  exact vanishingAverageConfidenceDelta_ennreal_tendsto_zero.prodMk
    (decayingExplorationAverageExploratoryBehaviorBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor)

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

noncomputable def decayingExplorationAverageExploratoryBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Set
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)) :=
  {trajectory |
    AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
          mdp baseVisitFloor n <
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
          mdp (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
            (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
              mdp baseVisitFloor n))
        (AdaptiveEpisodeBatchSource.decayingExplorationRate n)
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)}

theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real) (n : Nat)
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
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
    let episodes :=
      AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp rounds delta visitFloor
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
    let violationSet :=
      decayingExplorationAverageExploratoryBehaviorRegretViolationSet
        mdp initialState defaultState baseVisitFloor n
    MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent rounds delta) <=
        ENNReal.ofReal delta /\
      violationSet ⊆ source.adaptiveCumulativeCountBadEvent rounds delta /\
      source.trajectoryMeasure violationSet <= ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius
            explorationRate
            (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n) rounds <=
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
  let source := exploratorySource mdp initialState episodes initialTable
    defaultState countRadius explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  let violationSet :=
    decayingExplorationAverageExploratoryBehaviorRegretViolationSet
      mdp initialState defaultState baseVisitFloor n
  letI : StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp rounds delta visitFloor)) := by
    change StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))
    infer_instance
  letI : StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp rounds delta visitFloor)) := by
    change StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))
    infer_instance
  have hparent :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_scheduledAverageRecommendedExpectedRegret
      mdp initialState rounds delta visitFloor initialTable defaultState
      explorationRate (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
      support
      (AdaptiveEpisodeBatchSource.decayingExplorationUniformVisitFloor
        support hbaseFloor n)
      hrewardBound hhorizon
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
      (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor_pos
        mdp hbaseVisitFloor n)
  dsimp only at hparent
  rcases hparent with ⟨hmeasurable, hbadTail, houtside⟩
  have hbehaviorOutside : forall trajectory,
      trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
      (forall round : Fin rounds, forall state,
        mdp.optimalValueRemaining mdp.horizon le_rfl state <=
          (adaptiveCumulativeEmpiricalOptimisticPlanAt
            trajectory defaultState countRadius round).upperValueRemaining
              mdp.horizon le_rfl state) /\
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
          (initialState := initialState) trajectory defaultState countRadius
          explorationRate
          (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n) rounds <=
        AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
          mdp baseVisitFloor n := by
    intro trajectory htrajectory
    have hrecommendation := houtside trajectory htrajectory
    refine ⟨hrecommendation.1, ?_⟩
    have htransport :=
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret_le
        (initialState := initialState) trajectory defaultState countRadius
        explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        1 hrewardBound rounds
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n)
    apply htransport.trans
    unfold AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      AdaptiveEpisodeBatchSource.decayingExplorationAverageRecommendedExpectedRegretBound
      AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    exact add_le_add hrecommendation.2 le_rfl
  have hsubset :
      violationSet ⊆ source.adaptiveCumulativeCountBadEvent rounds delta := by
    intro trajectory hviolation
    by_contra houtsideBad
    have hbound := (hbehaviorOutside trajectory houtsideBad).2
    exact (not_lt_of_ge hbound) hviolation
  have hviolationTail :
      source.trajectoryMeasure violationSet <= ENNReal.ofReal delta :=
    (measure_mono hsubset).trans hbadTail
  exact ⟨hmeasurable, hbadTail, hsubset, hviolationTail, hbehaviorOutside⟩

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
