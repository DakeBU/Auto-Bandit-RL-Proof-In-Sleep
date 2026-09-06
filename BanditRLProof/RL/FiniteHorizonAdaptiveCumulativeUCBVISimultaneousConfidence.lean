import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIConfidenceTuning
import BanditRLProof.ProbabilityUnionBound

/-!
# Finite same-source confidence family for cumulative UCBVI-CH

The family contains two genuinely generated transition coordinates:

* every next-state singleton, with its Bernoulli variance; and
* the normalized optimal continuation value at every stage.

The second coordinate is not postulated as an external confidence premise.  It
is proved from the same recursive episode source and is linked to the singleton
residual family by the exact finite linear identity in
`FiniteHorizonAdaptiveCumulativeUCBVITransitionValueConfidence`.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveCumulativeHoeffdingUCBVI

/-- One peeled singleton-transition query.  `count` encodes the positive
actual visit count `count + 1`. -/
structure BernsteinCoordinateIndex (mdp : MDP State Action) (episodes : Nat) where
  round : Fin episodes
  state : State
  action : Action
  nextState : State
  count : Fin (episodes * mdp.horizon)
  deriving Fintype, DecidableEq

/-- One peeled optimal-tail scalar query. -/
structure OptimalTailIndex (mdp : MDP State Action) (episodes : Nat) where
  round : Fin episodes
  stage : Fin mdp.horizon
  state : State
  action : Action
  count : Fin (episodes * mdp.horizon)
  deriving Fintype, DecidableEq

namespace AdaptiveEpisodeBatchSource

noncomputable def bernsteinCoordinateFailureEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (logBudget : Real) (index : BernsteinCoordinateIndex mdp episodes) :
    Set (EpisodeBatchTrajectory mdp 1) :=
  let varianceBudget := mdp.transitionCoordinateVariance
      index.state index.action index.nextState * (index.count + 1 : Nat)
  {trajectory |
    bernsteinCoordinateThreshold logBudget varianceBudget <=
        |∑ i ∈ Finset.range (index.round + 1),
          source.aggregateTransitionResidualIncrement
            index.state index.action index.nextState i trajectory| ∧
      (∑ i ∈ Finset.range (index.round + 1),
          source.aggregateVisitIncrement index.state index.action i trajectory) <=
        (index.count + 1 : Nat)}

noncomputable def optimalTailFailureEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (logBudget : Real) (index : OptimalTailIndex mdp episodes) :
    Set (EpisodeBatchTrajectory mdp 1) :=
  {trajectory |
    logBudget * Real.sqrt (index.count + 1 : Nat) <=
        |∑ i ∈ Finset.range (index.round + 1),
          source.aggregateTransitionFunctionalResidualIncrement
            (mdp.optimalTailProbe index.stage)
            index.state index.action i trajectory| ∧
      (∑ i ∈ Finset.range (index.round + 1),
          source.aggregateVisitIncrement index.state index.action i trajectory) <=
        (index.count + 1 : Nat)}

/-- The complete finite same-source transition confidence failure set. -/
noncomputable def simultaneousTransitionFailureEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (episodes : Nat) (logBudget : Real) :
    Set (EpisodeBatchTrajectory mdp 1) :=
  (⋃ index : BernsteinCoordinateIndex mdp episodes,
      bernsteinCoordinateFailureEvent source logBudget index) ∪
  (⋃ index : OptimalTailIndex mdp episodes,
      optimalTailFailureEvent source logBudget index)

theorem trajectoryMeasure_bernsteinCoordinateFailureEvent_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (logBudget : Real) (hlog : 0 < logBudget)
    (index : BernsteinCoordinateIndex mdp episodes) :
    source.trajectoryMeasure
        (bernsteinCoordinateFailureEvent source logBudget index) <=
      2 * ENNReal.ofReal (Real.exp (-2 * logBudget)) := by
  let varianceBudget : Real := mdp.transitionCoordinateVariance
      index.state index.action index.nextState * (index.count + 1 : Nat)
  let tilt := bernsteinTilt logBudget varianceBudget
  have hvariance : 0 <= varianceBudget := by
    exact mul_nonneg
      (mdp.transitionCoordinateVariance_nonneg _ _ _)
      (Nat.cast_nonneg _)
  have htail := source.measure_abs_aggregateTransitionResidualSum_ge_inter_visitSum_le_variance
    index.state index.action index.nextState (index.round + 1)
    tilt (bernsteinCoordinateThreshold logBudget varianceBudget)
    (index.count + 1 : Nat)
    (bernsteinTilt_pos hlog hvariance)
    (bernsteinTilt_le_one _ _)
  have hexponent := bernsteinTilt_exponent_le hlog hvariance
  have hexponent' :
      -tilt * bernsteinCoordinateThreshold logBudget varianceBudget +
          tilt ^ 2 * varianceBudget <= -2 * logBudget := by
    simpa [tilt] using hexponent
  have harg :
      -tilt * bernsteinCoordinateThreshold logBudget varianceBudget +
          tilt ^ 2 * mdp.transitionCoordinateVariance
            index.state index.action index.nextState * (index.count + 1 : Nat) <=
        -2 * logBudget := by
    rw [show tilt ^ 2 * mdp.transitionCoordinateVariance
          index.state index.action index.nextState * (index.count + 1 : Nat) =
        tilt ^ 2 * varianceBudget by simp [varianceBudget, mul_assoc]]
    exact hexponent'
  calc
    source.trajectoryMeasure
        (bernsteinCoordinateFailureEvent source logBudget index) <=
      2 * ENNReal.ofReal
        (Real.exp (-tilt * bernsteinCoordinateThreshold logBudget varianceBudget +
          tilt ^ 2 * mdp.transitionCoordinateVariance
            index.state index.action index.nextState * (index.count + 1 : Nat))) := by
      simpa [bernsteinCoordinateFailureEvent, varianceBudget, tilt, mul_assoc] using htail
    _ <= 2 * ENNReal.ofReal (Real.exp (-2 * logBudget)) := by
      apply mul_le_mul_left'
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact harg

noncomputable def functionalTilt (logBudget visitBudget : Real) : Real :=
  4 * logBudget / Real.sqrt visitBudget

theorem functionalTilt_pos
    {logBudget visitBudget : Real}
    (hlog : 0 < logBudget) (hvisit : 0 < visitBudget) :
    0 < functionalTilt logBudget visitBudget := by
  unfold functionalTilt
  exact div_pos (mul_pos (by norm_num) hlog) (Real.sqrt_pos.2 hvisit)

theorem functionalTilt_exponent_eq
    {logBudget visitBudget : Real}
    (hvisit : 0 < visitBudget) :
    -functionalTilt logBudget visitBudget *
          (logBudget * Real.sqrt visitBudget) +
        (functionalTilt logBudget visitBudget ^ 2 / 8) * visitBudget =
      -2 * logBudget ^ 2 := by
  have hsqrt : Real.sqrt visitBudget ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hvisit)
  have hsqrtSq : Real.sqrt visitBudget ^ 2 = visitBudget :=
    Real.sq_sqrt hvisit.le
  unfold functionalTilt
  field_simp
  nlinarith

theorem trajectoryMeasure_optimalTailFailureEvent_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (hreward : ∀ state action, |mdp.reward state action| <= 1)
    (logBudget : Real) (hlog : 0 < logBudget)
    (index : OptimalTailIndex mdp episodes) :
    source.trajectoryMeasure
        (optimalTailFailureEvent source logBudget index) <=
      2 * ENNReal.ofReal (Real.exp (-2 * logBudget ^ 2)) := by
  let visitBudget : Real := (index.count + 1 : Nat)
  let tilt := functionalTilt logBudget visitBudget
  have hvisit : 0 < visitBudget := by
    change 0 < ((index.count + 1 : Nat) : Real)
    positivity
  have hprobe : ∀ nextState,
      mdp.optimalTailProbe index.stage nextState ∈ Set.Icc (0 : Real) 1 :=
    mdp.optimalTailProbe_mem_Icc hreward index.stage
  have htail := source.measure_abs_aggregateTransitionFunctionalResidualSum_ge_inter_visitSum_le
    (mdp.optimalTailProbe index.stage) hprobe index.state index.action
    (index.round + 1) tilt (logBudget * Real.sqrt visitBudget) visitBudget
    (functionalTilt_pos hlog hvisit)
  calc
    source.trajectoryMeasure (optimalTailFailureEvent source logBudget index) <=
      2 * ENNReal.ofReal
        (Real.exp (-tilt * (logBudget * Real.sqrt visitBudget) +
          (tilt ^ 2 / 8) * visitBudget)) := by
      simpa [optimalTailFailureEvent, visitBudget, tilt] using htail
    _ = 2 * ENNReal.ofReal (Real.exp (-2 * logBudget ^ 2)) := by
      rw [functionalTilt_exponent_eq hvisit]

/-- A transparent finite-union bound.  The later UCBVI specialization proves
that the displayed right hand side is at most its allotted fraction of
`delta`; keeping this intermediate theorem exact makes the event accounting
auditable. -/
theorem trajectoryMeasure_simultaneousTransitionFailureEvent_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (hreward : ∀ state action, |mdp.reward state action| <= 1)
    (episodes : Nat) (logBudget : Real) (hlog : 0 < logBudget) :
    source.trajectoryMeasure
        (simultaneousTransitionFailureEvent source episodes logBudget) <=
      (Fintype.card (BernsteinCoordinateIndex mdp episodes) : ENNReal) *
          (2 * ENNReal.ofReal (Real.exp (-2 * logBudget))) +
        (Fintype.card (OptimalTailIndex mdp episodes) : ENNReal) *
          (2 * ENNReal.ofReal (Real.exp (-2 * logBudget ^ 2))) := by
  unfold simultaneousTransitionFailureEvent
  calc
    source.trajectoryMeasure
        ((⋃ index : BernsteinCoordinateIndex mdp episodes,
            bernsteinCoordinateFailureEvent source logBudget index) ∪
          (⋃ index : OptimalTailIndex mdp episodes,
            optimalTailFailureEvent source logBudget index)) <=
      source.trajectoryMeasure
          (⋃ index : BernsteinCoordinateIndex mdp episodes,
            bernsteinCoordinateFailureEvent source logBudget index) +
        source.trajectoryMeasure
          (⋃ index : OptimalTailIndex mdp episodes,
            optimalTailFailureEvent source logBudget index) := measure_union_le _ _
    _ <= (∑ _index : BernsteinCoordinateIndex mdp episodes,
          2 * ENNReal.ofReal (Real.exp (-2 * logBudget))) +
        (∑ _index : OptimalTailIndex mdp episodes,
          2 * ENNReal.ofReal (Real.exp (-2 * logBudget ^ 2))) := by
      gcongr
      · refine (ProbabilityUnionBound.measure_iUnion_fintype_le_sum
          source.trajectoryMeasure _).trans ?_
        exact Finset.sum_le_sum fun index _ =>
          trajectoryMeasure_bernsteinCoordinateFailureEvent_le
            source logBudget hlog index
      · refine (ProbabilityUnionBound.measure_iUnion_fintype_le_sum
          source.trajectoryMeasure _).trans ?_
        exact Finset.sum_le_sum fun index _ =>
          trajectoryMeasure_optimalTailFailureEvent_le
            source hreward logBudget hlog index
    _ = _ := by simp [nsmul_eq_mul]

/-- Outside the joint event, every peeled singleton residual is strictly below
its variance-sensitive threshold whenever the peel equals the actual count. -/
theorem abs_coordinateResidual_lt_of_not_mem_simultaneousTransitionFailureEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {logBudget : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (htrajectory : trajectory ∉
      simultaneousTransitionFailureEvent source episodes logBudget)
    (index : BernsteinCoordinateIndex mdp episodes)
    (hcount :
      (∑ i ∈ Finset.range (index.round + 1),
          source.aggregateVisitIncrement index.state index.action i trajectory) =
        (index.count + 1 : Nat)) :
    |∑ i ∈ Finset.range (index.round + 1),
        source.aggregateTransitionResidualIncrement
          index.state index.action index.nextState i trajectory| <
      bernsteinCoordinateThreshold logBudget
        (mdp.transitionCoordinateVariance
          index.state index.action index.nextState * (index.count + 1 : Nat)) := by
  apply lt_of_not_ge
  intro hge
  apply htrajectory
  apply Set.mem_union_left
  exact Set.mem_iUnion.2 ⟨index, hge, hcount.le⟩

/-- The sharp optimal-tail scalar coordinate is extracted from the same joint
event, again at its exact actual-count peel. -/
theorem abs_optimalTailResidual_lt_of_not_mem_simultaneousTransitionFailureEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {logBudget : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (htrajectory : trajectory ∉
      simultaneousTransitionFailureEvent source episodes logBudget)
    (index : OptimalTailIndex mdp episodes)
    (hcount :
      (∑ i ∈ Finset.range (index.round + 1),
          source.aggregateVisitIncrement index.state index.action i trajectory) =
        (index.count + 1 : Nat)) :
    |∑ i ∈ Finset.range (index.round + 1),
        source.aggregateTransitionFunctionalResidualIncrement
          (mdp.optimalTailProbe index.stage)
          index.state index.action i trajectory| <
      logBudget * Real.sqrt (index.count + 1 : Nat) := by
  apply lt_of_not_ge
  intro hge
  apply htrajectory
  apply Set.mem_union_right
  exact Set.mem_iUnion.2 ⟨index, hge, hcount.le⟩

end AdaptiveEpisodeBatchSource

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
