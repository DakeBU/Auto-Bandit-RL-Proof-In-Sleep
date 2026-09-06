import BanditRLProof.RL.FiniteHorizonIIDSimultaneousCountConfidence

/-!
# Eligible positive visit counts for finite-horizon iid batches

This module turns the compiled simultaneous visit-count deviation into a
positive-denominator guarantee on an arbitrary finite set of eligible visit
coordinates. Eligibility carries the necessary strict expected-count margin;
unreachable coordinates are not assigned a false positivity conclusion.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/-- One stage/state/action coordinate whose empirical visit count may be used
as a denominator. -/
structure VisitCoordinate (mdp : MDP State Action) where
  stage : Fin mdp.horizon
  state : State
  action : Action
  deriving DecidableEq, Fintype

namespace VisitCoordinate

/-- Realized visit count selected by a visit coordinate. -/
def count {mdp : MDP State Action} (coordinate : VisitCoordinate mdp)
    {episodes : Nat} (batch : EpisodeBatch mdp episodes) : Nat :=
  batch.visitCount coordinate.stage coordinate.state coordinate.action

/-- Genuine expected visit count under the fixed-policy single-episode law. -/
noncomputable def expectedCount
    {mdp : MDP State Action} (coordinate : VisitCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) : Real :=
  (episodes : Real) *
    policy.stageVisitProbability initialState
      coordinate.stage coordinate.state coordinate.action

/-- Event that the selected visit coordinate has zero realized count. -/
def zeroCountEvent
    {mdp : MDP State Action} (coordinate : VisitCoordinate mdp)
    (episodes : Nat) : Set (EpisodeBatch mdp episodes) :=
  {batch | (coordinate.count batch : Real) = 0}

omit [Nonempty State] [Nonempty Action] in
/-- A selected zero visit-count event is measurable. -/
theorem measurableSet_zeroCountEvent
    {mdp : MDP State Action} (coordinate : VisitCoordinate mdp)
    (episodes : Nat) :
    MeasurableSet (coordinate.zeroCountEvent episodes) := by
  have hmeas : Measurable fun batch : EpisodeBatch mdp episodes =>
      (coordinate.count batch : Real) := by
    simpa [count] using
      (MarkovPolicy.measurable_cast_visitCount
        (mdp := mdp) (episodes := episodes)
        coordinate.stage coordinate.state coordinate.action)
  change MeasurableSet
    {batch : EpisodeBatch mdp episodes | (coordinate.count batch : Real) = 0}
  exact measurableSet_eq_fun hmeas measurable_const

end VisitCoordinate

/-- Union of zero-count events over a finite caller-selected coordinate set. -/
def eligibleZeroVisitCountEvent
    {mdp : MDP State Action} (episodes : Nat)
    (eligible : Finset (VisitCoordinate mdp)) :
    Set (EpisodeBatch mdp episodes) :=
  ⋃ coordinate ∈ eligible, coordinate.zeroCountEvent episodes

omit [Nonempty State] [Nonempty Action] in
/-- The finite eligible zero-count union is measurable. -/
theorem measurableSet_eligibleZeroVisitCountEvent
    {mdp : MDP State Action} (episodes : Nat)
    (eligible : Finset (VisitCoordinate mdp)) :
    MeasurableSet (eligibleZeroVisitCountEvent episodes eligible) := by
  unfold eligibleZeroVisitCountEvent
  exact MeasurableSet.iUnion fun coordinate =>
    MeasurableSet.iUnion fun _ =>
      coordinate.measurableSet_zeroCountEvent episodes

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Outside the eligible zero-count union, every selected Nat count is positive. -/
theorem visitCoordinate_count_pos_of_not_mem_eligibleZeroVisitCountEvent
    {mdp : MDP State Action} {episodes : Nat}
    (eligible : Finset (VisitCoordinate mdp))
    (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉ eligibleZeroVisitCountEvent episodes eligible)
    (coordinate : VisitCoordinate mdp) (hcoordinate : coordinate ∈ eligible) :
    0 < coordinate.count batch := by
  by_contra hcount
  have hzero : coordinate.count batch = 0 :=
    Nat.eq_zero_of_not_pos hcount
  apply hbatch
  apply Set.mem_iUnion.2
  refine ⟨coordinate, Set.mem_iUnion.2 ⟨hcoordinate, ?_⟩⟩
  change (coordinate.count batch : Real) = 0
  exact_mod_cast hzero

namespace MarkovPolicy

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A strict expected-count margin turns the simultaneous deviation bound into
a positive realized visit count. -/
theorem visitCoordinate_count_pos_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (coordinate : VisitCoordinate mdp)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      coordinate.expectedCount policy initialState episodes) :
    0 < coordinate.count batch := by
  by_contra hcount
  have hzero : coordinate.count batch = 0 :=
    Nat.eq_zero_of_not_pos hcount
  have hradius_nonneg :
      0 ≤ simultaneousCountConfidenceRadius mdp episodes delta :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hexpected_pos :
      0 < coordinate.expectedCount policy initialState episodes :=
    lt_of_le_of_lt hradius_nonneg hmargin
  have hdeviation :=
    policy.visitCount_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch coordinate.stage coordinate.state coordinate.action
  change |(coordinate.count batch : Real) -
      coordinate.expectedCount policy initialState episodes| <
    simultaneousCountConfidenceRadius mdp episodes delta at hdeviation
  have hexpected_lt_radius :
      coordinate.expectedCount policy initialState episodes <
        simultaneousCountConfidenceRadius mdp episodes delta := by
    simpa [hzero, abs_of_pos hexpected_pos] using hdeviation
  exact (not_lt_of_ge (le_of_lt hmargin)) hexpected_lt_radius

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Under the eligible margins, every eligible zero-count outcome lies in the
already-budgeted simultaneous bad event. -/
theorem eligibleZeroVisitCountEvent_subset_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real}
    (eligible : Finset (VisitCoordinate mdp))
    (hmargin : ∀ coordinate ∈ eligible,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes) :
    eligibleZeroVisitCountEvent episodes eligible ⊆
      policy.simultaneousCountBadEvent initialState episodes delta := by
  intro batch hzero
  rcases Set.mem_iUnion.1 hzero with ⟨coordinate, hzero⟩
  rcases Set.mem_iUnion.1 hzero with ⟨hcoordinate, hzero⟩
  by_contra hbatch
  have hpos :=
    policy.visitCoordinate_count_pos_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch coordinate (hmargin coordinate hcoordinate)
  have hzeroReal : (coordinate.count batch : Real) = 0 := by
    simpa [VisitCoordinate.zeroCountEvent] using hzero
  have hzeroNat : coordinate.count batch = 0 := by
    exact_mod_cast hzeroReal
  exact (Nat.ne_of_gt hpos) hzeroNat

omit [Nonempty State] [Nonempty Action] in
/-- The eligible zero-count union inherits the simultaneous global-delta tail. -/
theorem iidEpisodeBatch_eligibleZeroVisitCountEvent_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (eligible : Finset (VisitCoordinate mdp))
    (hmargin : ∀ coordinate ∈ eligible,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes) :
    (policy.iidEpisodeBatchMeasure initialState episodes)
        (eligibleZeroVisitCountEvent episodes eligible) ≤
      ENNReal.ofReal delta := by
  calc
    (policy.iidEpisodeBatchMeasure initialState episodes)
        (eligibleZeroVisitCountEvent episodes eligible) ≤
        (policy.iidEpisodeBatchMeasure initialState episodes)
          (policy.simultaneousCountBadEvent initialState episodes delta) :=
      measure_mono
        (policy.eligibleZeroVisitCountEvent_subset_simultaneousCountBadEvent
          initialState eligible hmargin)
    _ ≤ ENNReal.ofReal delta :=
      policy.iidEpisodeBatch_simultaneousCountBadEvent_le
        initialState episodes hepisodes delta hdelta hdelta_le_one

omit [Nonempty State] [Nonempty Action] in
/--
Route endpoint: eligible zero counts have global-delta probability, and every
eligible denominator is positive outside that exact zero-count event. The
named subset theorem separately embeds this event in the compiled simultaneous
bad event.
-/
theorem iidEpisodeBatch_eligible_visit_count_positivity
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (eligible : Finset (VisitCoordinate mdp))
    (hmargin : ∀ coordinate ∈ eligible,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes) :
    MeasurableSet (eligibleZeroVisitCountEvent episodes eligible) ∧
      (policy.iidEpisodeBatchMeasure initialState episodes)
          (eligibleZeroVisitCountEvent episodes eligible) ≤
        ENNReal.ofReal delta ∧
      ∀ batch ∉ eligibleZeroVisitCountEvent episodes eligible,
        ∀ coordinate ∈ eligible, 0 < coordinate.count batch := by
  refine ⟨measurableSet_eligibleZeroVisitCountEvent episodes eligible,
    policy.iidEpisodeBatch_eligibleZeroVisitCountEvent_le
      initialState episodes hepisodes delta hdelta hdelta_le_one
      eligible hmargin, ?_⟩
  intro batch hbatch coordinate hcoordinate
  exact visitCoordinate_count_pos_of_not_mem_eligibleZeroVisitCountEvent
    eligible batch hbatch coordinate hcoordinate

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
