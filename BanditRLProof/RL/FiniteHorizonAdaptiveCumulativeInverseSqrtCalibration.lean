import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeCountMartingaleConfidence
import BanditRLProof.RL.FiniteHorizonExploratoryPathSupportExplicitCalibration

/-!
# Adaptive cumulative inverse-square-root calibration

This module calibrates the cumulative count-martingale confidence producer to
a concrete count-dependent optimistic planner.  Path-support exploration gives
every adaptive batch a common predictable visit floor.  Outside the compiled
global count event, the accumulated realized visits exceed that predictable
floor minus the cumulative confidence radius.

The usable planner radius is `budget` at zero visits and
`min budget (scale / sqrt(count))` after the first visit.  Separating the
zero-count value-envelope cap from the inverse-square-root scale avoids the
uninhabitable one-scale cover.  A deterministic roundwise two-scale calibration
then supplies both cap and inverse-square-root covers.  The terminal remains
about recommended-policy expected regret, not behavior or realized regret.
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

namespace TransitionCountRadius

/--
A concrete count radius: the supplied budget at zero visits and inverse-square
root decay after the first visit.
-/
noncomputable def inverseSqrt (budget : Real) (hbudget : 0 <= budget) :
    TransitionCountRadius where
  radius count := if count = 0 then budget else budget / Real.sqrt count
  nonneg count := by
    split_ifs
    · exact hbudget
    · exact div_nonneg hbudget (Real.sqrt_nonneg _)
  antitone := by
    intro left right hle
    by_cases hleft : left = 0
    · subst left
      by_cases hright : right = 0
      · simp [hright]
      · have hrightOne : (1 : Real) <= right := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hright)
        have hsqrtOne : (1 : Real) <= Real.sqrt right :=
          Real.one_le_sqrt.mpr hrightOne
        simp only [if_neg hright]
        exact div_le_self hbudget hsqrtOne
    · have hright : right ≠ 0 := by omega
      have hleftPos : (0 : Real) < left := by
        exact_mod_cast (Nat.pos_of_ne_zero hleft)
      have hsqrtLeftPos : 0 < Real.sqrt (left : Real) :=
        Real.sqrt_pos.2 hleftPos
      have hsqrtLe : Real.sqrt (left : Real) <= Real.sqrt (right : Real) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hle)
      simp only [if_neg hleft, if_neg hright]
      exact div_le_div_of_nonneg_left hbudget hsqrtLeftPos hsqrtLe

/-- The inverse-square-root radius exposes its supplied zero-count budget. -/
@[simp] theorem inverseSqrt_radius_zero (budget : Real) (hbudget : 0 <= budget) :
    (inverseSqrt budget hbudget).radius 0 = budget := by
  simp [inverseSqrt]

/-- Positive counts use the genuine inverse-square-root branch. -/
theorem inverseSqrt_radius_of_pos (budget : Real) (hbudget : 0 <= budget)
    {count : Nat} (hcount : 0 < count) :
    (inverseSqrt budget hbudget).radius count =
      budget / Real.sqrt count := by
  simp [inverseSqrt, Nat.ne_of_gt hcount]

/--
A usable capped inverse-square-root radius.  `budget` controls the zero-count
value envelope, while `scale` controls the statistical decay after enough
visits; the cap preserves antitonicity across the first visit.
-/
noncomputable def cappedInverseSqrt (budget scale : Real)
    (hbudget : 0 <= budget) (hscale : 0 <= scale) : TransitionCountRadius where
  radius count :=
    if count = 0 then budget else min budget (scale / Real.sqrt count)
  nonneg count := by
    split_ifs
    · exact hbudget
    · exact le_min hbudget (div_nonneg hscale (Real.sqrt_nonneg _))
  antitone := by
    intro left right hle
    by_cases hleft : left = 0
    · subst left
      by_cases hright : right = 0
      · simp [hright]
      · simp only [if_neg hright]
        exact min_le_left _ _
    · have hright : right ≠ 0 := by omega
      have hleftPos : (0 : Real) < left := by
        exact_mod_cast (Nat.pos_of_ne_zero hleft)
      have hsqrtLeftPos : 0 < Real.sqrt (left : Real) :=
        Real.sqrt_pos.2 hleftPos
      have hsqrtLe : Real.sqrt (left : Real) <= Real.sqrt (right : Real) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hle)
      simp only [if_neg hleft, if_neg hright]
      exact min_le_min_left budget
        (div_le_div_of_nonneg_left hscale hsqrtLeftPos hsqrtLe)

@[simp] theorem cappedInverseSqrt_radius_zero
    (budget scale : Real) (hbudget : 0 <= budget) (hscale : 0 <= scale) :
    (cappedInverseSqrt budget scale hbudget hscale).radius 0 = budget := by
  simp [cappedInverseSqrt]

theorem cappedInverseSqrt_radius_of_pos
    (budget scale : Real) (hbudget : 0 <= budget) (hscale : 0 <= scale)
    {count : Nat} (hcount : 0 < count) :
    (cappedInverseSqrt budget scale hbudget hscale).radius count =
      min budget (scale / Real.sqrt count) := by
  simp [cappedInverseSqrt, Nat.ne_of_gt hcount]

end TransitionCountRadius

namespace AdaptiveEpisodeBatchSource

/-- Predictable cumulative visit floor supplied by one path-support batch floor. -/
def cumulativePathVisitExpectedFloor
    (episodes prefixRounds : Nat) (visitFloor : Real) : Real :=
  (prefixRounds : Real) * (episodes : Real) * visitFloor

/-- Predictable visit floor after subtracting the cumulative confidence radius. -/
noncomputable def cumulativePathVisitLowerMargin
    (mdp : MDP State Action) (episodes rounds : Nat)
    (delta visitFloor : Real) (round : Fin rounds) : Real :=
  cumulativePathVisitExpectedFloor episodes (round + 1) visitFloor -
    cumulativeCoordinateConfidenceRadius episodes (round + 1)
      (cumulativeCountLocalDelta mdp rounds delta)

/-- Deterministic selected-radius envelope obtained from the lower visit margin. -/
noncomputable def cumulativeInverseSqrtRadiusEnvelope
    (mdp : MDP State Action) (episodes rounds : Nat)
    (delta visitFloor budget scale : Real) (round : Fin rounds) : Real :=
  min budget (scale / Real.sqrt
    (cumulativePathVisitLowerMargin mdp episodes rounds delta visitFloor round))

/--
Scalar regularity needed to fit all transition-coordinate errors under the
inverse-square-root planner radius.  It is deterministic and roundwise; path
support and the martingale event supply the corresponding realized counts.
-/
structure CumulativeInverseSqrtPathCalibration
    (mdp : MDP State Action) (episodes rounds : Nat)
    (delta visitFloor rewardBound budget scale : Real) : Prop where
  visitFloor_pos : 0 < visitFloor
  rewardBound_nonneg : 0 <= rewardBound
  budget_nonneg : 0 <= budget
  scale_nonneg : 0 <= scale
  lowerMargin_pos : forall round : Fin rounds,
    0 < cumulativePathVisitLowerMargin
      mdp episodes rounds delta visitFloor round
  coverBudget : forall round : Fin rounds,
    (Fintype.card State : Real) *
          (2 * cumulativeCoordinateConfidenceRadius episodes (round + 1)
            (cumulativeCountLocalDelta mdp rounds delta)) *
          ((mdp.horizon : Real) * (rewardBound + budget)) <=
      budget * cumulativePathVisitLowerMargin
        mdp episodes rounds delta visitFloor round
  coverScale : forall round : Fin rounds,
    (Fintype.card State : Real) *
          (2 * cumulativeCoordinateConfidenceRadius episodes (round + 1)
            (cumulativeCountLocalDelta mdp rounds delta)) *
          ((mdp.horizon : Real) * (rewardBound + budget)) <=
      scale * Real.sqrt
        (cumulativePathVisitLowerMargin
          mdp episodes rounds delta visitFloor round)

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

omit [Nonempty State] in
/-- Every adaptive exploratory batch retains the common path-support visit floor. -/
theorem exploratorySource_coordinateMeanAt_visit_ge_pathFloor
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (round : Nat) (trajectory : EpisodeBatchTrajectory mdp episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (episodes : Real) * visitFloor <=
      (exploratorySource mdp initialState episodes initialTable defaultState
        countRadius explorationRate hexplorationRate).coordinateMeanAt
          (.visit stage state action) round trajectory := by
  cases round with
  | zero =>
      simpa [AdaptiveEpisodeBatchSource.coordinateMeanAt,
        exploratorySource, CountCoordinate.policyMean,
        VisitCoordinate.expectedCount] using
        (initialTable.uniformVisitFloor_expectedCount_le initialState episodes
          support explorationRate hexplorationRate visitFloor hfloor
          ({ stage := stage, state := state, action := action } : VisitCoordinate mdp))
  | succ n =>
      rw [AdaptiveEpisodeBatchSource.coordinateMeanAt,
        AdaptiveEpisodeBatchSource.coordinateKernelMean_eq_policyMean]
      simpa [exploratorySource, CountCoordinate.policyMean,
        VisitCoordinate.expectedCount] using
        ((successorTable defaultState countRadius n
            (Preorder.frestrictLe n trajectory)).uniformVisitFloor_expectedCount_le
          initialState episodes support explorationRate hexplorationRate
          visitFloor hfloor
          ({ stage := stage, state := state, action := action } : VisitCoordinate mdp))

omit [Nonempty State] in
/-- The common batch floor sums to a predictable cumulative visit floor. -/
theorem exploratorySource_cumulativeCoordinateMean_visit_ge_pathFloor
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (prefixRounds : Nat) (trajectory : EpisodeBatchTrajectory mdp episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    AdaptiveEpisodeBatchSource.cumulativePathVisitExpectedFloor
        episodes prefixRounds visitFloor <=
      (exploratorySource mdp initialState episodes initialTable defaultState
        countRadius explorationRate hexplorationRate).cumulativeCoordinateMean
          (.visit stage state action) prefixRounds trajectory := by
  unfold AdaptiveEpisodeBatchSource.cumulativePathVisitExpectedFloor
    AdaptiveEpisodeBatchSource.cumulativeCoordinateMean
  calc
    (prefixRounds : Real) * (episodes : Real) * visitFloor =
        ∑ round ∈ Finset.range prefixRounds,
          (episodes : Real) * visitFloor := by
      simp
      ring
    _ <= ∑ round ∈ Finset.range prefixRounds,
          (exploratorySource mdp initialState episodes initialTable defaultState
            countRadius explorationRate hexplorationRate).coordinateMeanAt
              (.visit stage state action) round trajectory := by
      apply Finset.sum_le_sum
      intro round _hround
      exact exploratorySource_coordinateMeanAt_visit_ge_pathFloor
        mdp initialState episodes initialTable defaultState countRadius
        explorationRate hexplorationRate support visitFloor hfloor round trajectory
        stage state action

/-- Outside the global count event, every cumulative visit count exceeds its lower margin. -/
theorem exploratorySource_cumulativePathVisitLowerMargin_lt_visitCount
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes rounds : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor delta : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    {trajectory : EpisodeBatchTrajectory mdp episodes}
    (htrajectory : trajectory ∉
      (exploratorySource mdp initialState episodes initialTable defaultState
        countRadius explorationRate hexplorationRate).adaptiveCumulativeCountBadEvent
          rounds delta)
    (round : Fin rounds) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    AdaptiveEpisodeBatchSource.cumulativePathVisitLowerMargin
        mdp episodes rounds delta visitFloor round <
      ((cumulativeTransitionCountSummaryAt trajectory round).visitCount
        stage state action : Real) := by
  let source := exploratorySource mdp initialState episodes initialTable defaultState
    countRadius explorationRate hexplorationRate
  have hdeviation :=
    source.cumulativeCoordinateDeviation_abs_lt_of_not_mem_badEvent
      htrajectory round (.visit stage state action)
  rw [source.cumulativeCoordinateDeviation_eq_rawCount_sub_mean,
    AdaptiveEpisodeBatchSource.cumulativeCoordinateRawCount_visit] at hdeviation
  have hmean := exploratorySource_cumulativeCoordinateMean_visit_ge_pathFloor
    mdp initialState episodes initialTable defaultState countRadius
    explorationRate hexplorationRate support visitFloor hfloor (round + 1)
    trajectory stage state action
  rw [abs_lt] at hdeviation
  unfold AdaptiveEpisodeBatchSource.cumulativePathVisitLowerMargin
  dsimp only [source] at hdeviation hmean
  linarith

/-- Path support and the two-scale calibration discharge the full capped inverse-sqrt cover. -/
theorem exploratorySource_adaptiveCumulativeCountMartingaleCover_of_pathSupport_inverseSqrtCalibration
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes rounds : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor delta : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (rewardBound budget scale : Real)
    (calibration : AdaptiveEpisodeBatchSource.CumulativeInverseSqrtPathCalibration
      mdp episodes rounds delta visitFloor rewardBound budget scale) :
    AdaptiveEpisodeBatchSource.AdaptiveCumulativeCountMartingaleCover
      (rounds := rounds)
      (exploratorySource mdp initialState episodes initialTable defaultState
        (TransitionCountRadius.cappedInverseSqrt budget scale
          calibration.budget_nonneg calibration.scale_nonneg)
        explorationRate hexplorationRate)
      (TransitionCountRadius.cappedInverseSqrt budget scale
        calibration.budget_nonneg calibration.scale_nonneg)
      delta rewardBound := by
  intro trajectory htrajectory round remaining hremaining state action
  let stage := mdp.decisionStageRemaining remaining hremaining
  let summary := cumulativeTransitionCountSummaryAt trajectory round
  let visits := summary.visitCount stage state action
  let margin := AdaptiveEpisodeBatchSource.cumulativePathVisitLowerMargin
    mdp episodes rounds delta visitFloor round
  let radius := AdaptiveEpisodeBatchSource.cumulativeCoordinateConfidenceRadius
    episodes (round + 1)
      (AdaptiveEpisodeBatchSource.cumulativeCountLocalDelta mdp rounds delta)
  have hmarginPos : 0 < margin := calibration.lowerMargin_pos round
  have hmarginLt : margin < (visits : Real) := by
    simpa [margin, visits, summary, stage] using
      exploratorySource_cumulativePathVisitLowerMargin_lt_visitCount
        mdp initialState episodes rounds initialTable defaultState
        (TransitionCountRadius.cappedInverseSqrt budget scale
          calibration.budget_nonneg calibration.scale_nonneg)
        explorationRate hexplorationRate support visitFloor delta hfloor
        htrajectory round stage state action
  have hvisitsPosReal : (0 : Real) < visits := hmarginPos.trans hmarginLt
  have hvisitsPos : 0 < visits := by exact_mod_cast hvisitsPosReal
  have hvisitsNe : visits ≠ 0 := Nat.ne_of_gt hvisitsPos
  have hvisitsNonneg : (0 : Real) <= visits := le_of_lt hvisitsPosReal
  have hsqrtVisitsPos : 0 < Real.sqrt (visits : Real) :=
    Real.sqrt_pos.2 hvisitsPosReal
  have hsqrtMarginLe : Real.sqrt margin <= Real.sqrt (visits : Real) :=
    Real.sqrt_le_sqrt (le_of_lt hmarginLt)
  have hradiusNonneg : 0 <= radius := by
    exact Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hrewardBudgetNonneg : 0 <= rewardBound + budget :=
    add_nonneg calibration.rewardBound_nonneg calibration.budget_nonneg
  have hremainingReal : (remaining : Real) <= mdp.horizon := by
    exact_mod_cast (show remaining <= mdp.horizon by omega)
  have hscaleBudget :
      (Fintype.card State : Real) * (2 * radius) *
          ((remaining : Real) * (rewardBound + budget)) <=
        budget * margin := by
    calc
      (Fintype.card State : Real) * (2 * radius) *
            ((remaining : Real) * (rewardBound + budget)) <=
          (Fintype.card State : Real) * (2 * radius) *
            ((mdp.horizon : Real) * (rewardBound + budget)) := by
        gcongr
      _ <= budget * margin := by
        simpa [radius, margin] using calibration.coverBudget round
  have hscaleInverseSqrt :
      (Fintype.card State : Real) * (2 * radius) *
          ((remaining : Real) * (rewardBound + budget)) <=
        scale * Real.sqrt margin := by
    calc
      (Fintype.card State : Real) * (2 * radius) *
            ((remaining : Real) * (rewardBound + budget)) <=
          (Fintype.card State : Real) * (2 * radius) *
            ((mdp.horizon : Real) * (rewardBound + budget)) := by
        gcongr
      _ <= scale * Real.sqrt margin := by
        simpa [radius, margin] using calibration.coverScale round
  have hsumEq :
      (∑ nextState,
        AdaptiveEpisodeBatchSource.adaptiveCumulativeTransitionCoordinateRadius
            trajectory round delta stage state action nextState *
          empiricalFiniteBatchValueEnvelope rewardBound
            ((TransitionCountRadius.cappedInverseSqrt budget scale
              calibration.budget_nonneg calibration.scale_nonneg).radius 0)
              remaining) =
        ((Fintype.card State : Real) * (2 * radius) *
          ((remaining : Real) * (rewardBound + budget))) / (visits : Real) := by
    simp [AdaptiveEpisodeBatchSource.adaptiveCumulativeTransitionCoordinateRadius,
      empiricalFiniteBatchValueEnvelope, stage, summary, visits, radius,
      hvisitsNe]
    ring
  have hbudgetBound :
      ((Fintype.card State : Real) * (2 * radius) *
          ((remaining : Real) * (rewardBound + budget))) / (visits : Real) <=
        budget := by
    calc
      ((Fintype.card State : Real) * (2 * radius) *
          ((remaining : Real) * (rewardBound + budget))) / (visits : Real) <=
          (budget * margin) / (visits : Real) :=
        div_le_div_of_nonneg_right hscaleBudget hvisitsNonneg
      _ <= (budget * (visits : Real)) / (visits : Real) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_of_lt hmarginLt)
            calibration.budget_nonneg) hvisitsNonneg
      _ = budget := by field_simp
  have hinverseSqrtBound :
      ((Fintype.card State : Real) * (2 * radius) *
          ((remaining : Real) * (rewardBound + budget))) / (visits : Real) <=
        scale / Real.sqrt (visits : Real) := by
    calc
      ((Fintype.card State : Real) * (2 * radius) *
          ((remaining : Real) * (rewardBound + budget))) / (visits : Real) <=
          (scale * Real.sqrt margin) / (visits : Real) :=
        div_le_div_of_nonneg_right hscaleInverseSqrt hvisitsNonneg
      _ <= (scale * Real.sqrt (visits : Real)) / (visits : Real) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrtMarginLe calibration.scale_nonneg)
        hvisitsNonneg
      _ = scale / Real.sqrt (visits : Real) := by
        field_simp
        rw [Real.sq_sqrt hvisitsNonneg]
  rw [hsumEq, TransitionCountRadius.cappedInverseSqrt_radius_of_pos
    budget scale calibration.budget_nonneg calibration.scale_nonneg hvisitsPos]
  exact le_min hbudgetBound hinverseSqrtBound

/-- The selected capped inverse-sqrt radius is controlled by the lower-margin envelope. -/
theorem adaptiveCumulativeEmpiricalOptimisticPlanAt_selectedRadiusRemaining_le_inverseSqrtEnvelope
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes rounds : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor delta : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (rewardBound budget scale : Real)
    (calibration : AdaptiveEpisodeBatchSource.CumulativeInverseSqrtPathCalibration
      mdp episodes rounds delta visitFloor rewardBound budget scale)
    {trajectory : EpisodeBatchTrajectory mdp episodes}
    (htrajectory : trajectory ∉
      (exploratorySource mdp initialState episodes initialTable defaultState
        (TransitionCountRadius.cappedInverseSqrt budget scale
          calibration.budget_nonneg calibration.scale_nonneg)
        explorationRate hexplorationRate).adaptiveCumulativeCountBadEvent
          rounds delta)
    (round : Fin rounds) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    (adaptiveCumulativeEmpiricalOptimisticPlanAt trajectory defaultState
      (TransitionCountRadius.cappedInverseSqrt budget scale
        calibration.budget_nonneg calibration.scale_nonneg)
      round).selectedRadiusRemaining remaining hremaining state <=
      AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRadiusEnvelope
        mdp episodes rounds delta visitFloor budget scale round := by
  rw [adaptiveCumulativeEmpiricalOptimisticPlanAt,
    TransitionCountSummary.countRadiusOptimisticPlan_selectedRadiusRemaining]
  let stage := mdp.decisionStageRemaining remaining hremaining
  let summary := cumulativeTransitionCountSummaryAt trajectory round
  let countRadius := TransitionCountRadius.cappedInverseSqrt budget scale
    calibration.budget_nonneg calibration.scale_nonneg
  let plan := summary.countRadiusOptimisticPlan mdp defaultState countRadius
  let action := plan.optimisticAction stage
    (plan.upperValueRemaining remaining (by omega)) state
  let visits := summary.visitCount stage state action
  let margin := AdaptiveEpisodeBatchSource.cumulativePathVisitLowerMargin
    mdp episodes rounds delta visitFloor round
  have hmarginPos : 0 < margin := calibration.lowerMargin_pos round
  have hmarginLt : margin < (visits : Real) := by
    simpa [margin, visits, action, plan, countRadius, summary, stage] using
      exploratorySource_cumulativePathVisitLowerMargin_lt_visitCount
        mdp initialState episodes rounds initialTable defaultState countRadius
        explorationRate hexplorationRate support visitFloor delta hfloor
        htrajectory round stage state action
  have hvisitsPosReal : (0 : Real) < visits := hmarginPos.trans hmarginLt
  have hvisitsPos : 0 < visits := by exact_mod_cast hvisitsPosReal
  have hsqrtMarginPos : 0 < Real.sqrt margin := Real.sqrt_pos.2 hmarginPos
  have hsqrtMarginLe : Real.sqrt margin <= Real.sqrt (visits : Real) :=
    Real.sqrt_le_sqrt (le_of_lt hmarginLt)
  change countRadius.radius visits <=
    AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRadiusEnvelope
      mdp episodes rounds delta visitFloor budget scale round
  rw [TransitionCountRadius.cappedInverseSqrt_radius_of_pos
    budget scale calibration.budget_nonneg calibration.scale_nonneg hvisitsPos]
  unfold AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRadiusEnvelope
  exact min_le_min_left budget
    (div_le_div_of_nonneg_left calibration.scale_nonneg
      hsqrtMarginPos hsqrtMarginLe)

/--
Concrete route endpoint: path support and capped inverse-sqrt calibration produce one
measurable cumulative count event, optimism, and a round-indexed finite-sum bound
for recommended-policy expected regret.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_explicitRecommendedExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes rounds : Nat)
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (rewardBound budget scale : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (calibration : AdaptiveEpisodeBatchSource.CumulativeInverseSqrtPathCalibration
      mdp episodes rounds delta visitFloor rewardBound budget scale) :
    let countRadius :=
      TransitionCountRadius.cappedInverseSqrt budget scale
        calibration.budget_nonneg calibration.scale_nonneg
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate hexplorationRate
    MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent rounds delta) <=
        ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          ∑ round : Fin rounds,
            (mdp.horizon : Real) *
              (2 * AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRadiusEnvelope
                mdp episodes rounds delta visitFloor budget scale round) := by
  let countRadius :=
    TransitionCountRadius.cappedInverseSqrt budget scale
      calibration.budget_nonneg calibration.scale_nonneg
  have hcover : AdaptiveEpisodeBatchSource.AdaptiveCumulativeCountMartingaleCover
      (rounds := rounds)
      (exploratorySource mdp initialState episodes initialTable defaultState
        countRadius explorationRate hexplorationRate)
      countRadius delta rewardBound := by
    simpa [countRadius] using
      exploratorySource_adaptiveCumulativeCountMartingaleCover_of_pathSupport_inverseSqrtCalibration
        mdp initialState episodes rounds initialTable defaultState explorationRate
        hexplorationRate support visitFloor delta hfloor rewardBound budget scale calibration
  have hradius : forall trajectory,
      trajectory ∉
        (exploratorySource mdp initialState episodes initialTable defaultState
          countRadius explorationRate hexplorationRate).adaptiveCumulativeCountBadEvent
            rounds delta ->
      forall (round : Fin rounds) (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon) (state : State),
        (adaptiveCumulativeEmpiricalOptimisticPlanAt
          trajectory defaultState countRadius round).selectedRadiusRemaining
            remaining hremaining state <=
          AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRadiusEnvelope
            mdp episodes rounds delta visitFloor budget scale round := by
    intro trajectory htrajectory round remaining hremaining state
    simpa [countRadius] using
      adaptiveCumulativeEmpiricalOptimisticPlanAt_selectedRadiusRemaining_le_inverseSqrtEnvelope
        mdp initialState episodes rounds initialTable defaultState explorationRate
        hexplorationRate support visitFloor delta hfloor rewardBound budget scale calibration
        htrajectory round remaining hremaining state
  simpa [countRadius] using
    exploratorySource_trajectoryMeasure_cumulativeCountMartingale_optimism_and_explicitRecommendedExpectedRegret
      mdp initialState episodes rounds initialTable defaultState countRadius
      explorationRate hexplorationRate rewardBound hrewardBound hhorizon hrounds
      hepisodes delta hdelta hdelta_le_one hcover
      (AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRadiusEnvelope
        mdp episodes rounds delta visitFloor budget scale) hradius

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
