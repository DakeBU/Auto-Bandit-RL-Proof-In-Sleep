import BanditRLProof.RL.FiniteHorizonIIDCountConcentration
import BanditRLProof.ProbabilityUnionBound

/-!
# Simultaneous iid count confidence for finite-horizon RL

This module puts every finite visit and joint-transition count coordinate into
one index type and applies an equal-share finite union bound to the compiled
fixed-coordinate tails. The route remains fixed-policy iid. It does not form
visit-conditioned ratios or claim adaptive, anytime, or cumulative regret.
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

/--
Finite index of all visit and joint-transition count coordinates of an MDP.
-/
inductive CountCoordinate (mdp : MDP State Action) where
  | visit (stage : Fin mdp.horizon) (state : State) (action : Action)
  | transition (stage : Fin mdp.horizon) (state : State) (action : Action)
      (nextState : State)
  deriving DecidableEq, Fintype

namespace CountCoordinate

/-- Explicit finite-sum presentation of the two coordinate families. -/
def equivVisitSumTransition (mdp : MDP State Action) :
    CountCoordinate mdp ≃
      (Fin mdp.horizon × State × Action) ⊕
        (Fin mdp.horizon × State × Action × State) where
  toFun
    | .visit stage state action => Sum.inl (stage, (state, action))
    | .transition stage state action nextState =>
        Sum.inr (stage, (state, (action, nextState)))
  invFun
    | Sum.inl (stage, (state, action)) => .visit stage state action
    | Sum.inr (stage, (state, (action, nextState))) =>
        .transition stage state action nextState
  left_inv coordinate := by cases coordinate <;> rfl
  right_inv coordinate := by
    rcases coordinate with coordinate | coordinate
    · rcases coordinate with ⟨stage, state, action⟩
      rfl
    · rcases coordinate with ⟨stage, state, action, nextState⟩
      rfl

end CountCoordinate

/-- Number of visit and joint-transition coordinates in the simultaneous family. -/
def countCoordinateCard (mdp : MDP State Action) : Nat :=
  Fintype.card (CountCoordinate mdp)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The simultaneous family contains `H*S*A` visits and `H*S*A*S` transitions. -/
theorem countCoordinateCard_eq (mdp : MDP State Action) :
    countCoordinateCard mdp =
      mdp.horizon * Fintype.card State * Fintype.card Action +
        mdp.horizon * Fintype.card State * Fintype.card Action *
          Fintype.card State := by
  unfold countCoordinateCard
  rw [Fintype.card_congr (CountCoordinate.equivVisitSumTransition mdp)]
  simp [Nat.mul_assoc]

/-- Equal confidence share assigned to each count coordinate. -/
noncomputable def simultaneousCountDelta
    (mdp : MDP State Action) (delta : Real) : Real :=
  delta / (countCoordinateCard mdp : Real)

/-- Common count radius after allocating the global confidence budget equally. -/
noncomputable def simultaneousCountConfidenceRadius
    (mdp : MDP State Action) (episodes : Nat) (delta : Real) : Real :=
  Concentration.subGaussianSumConfidenceRadius
    (MarkovPolicy.iidBernoulliVarianceProxy episodes)
    (simultaneousCountDelta mdp delta)

namespace CountCoordinate

/-- Real count deviation selected by a visit or joint-transition coordinate. -/
noncomputable def deviation
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (batch : EpisodeBatch mdp episodes) : Real :=
  match coordinate with
  | .visit stage state action =>
      (batch.visitCount stage state action : Real) -
        (episodes : Real) *
          policy.stageVisitProbability initialState stage state action
  | .transition stage state action nextState =>
      (batch.transitionCount stage state action nextState : Real) -
        (episodes : Real) *
          policy.stageTransitionJointProbability initialState stage state action nextState

omit [Nonempty State] [Nonempty Action] in
/-- Every selected count deviation is measurable on the mapped batch space. -/
theorem measurable_deviation
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} :
    Measurable (coordinate.deviation policy initialState :
      EpisodeBatch mdp episodes → Real) := by
  cases coordinate with
  | visit stage state action =>
      exact policy.measurable_visitCountDeviation initialState stage state action
  | transition stage state action nextState =>
      exact policy.measurable_transitionCountDeviation
        initialState stage state action nextState

/-- Two-sided bad event for one selected coordinate at a supplied delta. -/
noncomputable def badEvent
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (coordinateDelta : Real) : Set (EpisodeBatch mdp episodes) :=
  {batch |
    Concentration.subGaussianSumConfidenceRadius
        (MarkovPolicy.iidBernoulliVarianceProxy episodes) coordinateDelta ≤
      |coordinate.deviation policy initialState batch|}

omit [Nonempty State] [Nonempty Action] in
/-- Every selected fixed-coordinate bad event is measurable. -/
theorem measurableSet_badEvent
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (coordinateDelta : Real) :
    MeasurableSet (coordinate.badEvent policy initialState episodes coordinateDelta) :=
  measurableSet_le measurable_const
    (coordinate.measurable_deviation policy initialState).abs

end CountCoordinate

namespace MarkovPolicy

omit [Nonempty State] [Nonempty Action] in
/-- The compiled marginal tail dispatches over the finite coordinate type. -/
theorem measure_countCoordinate_badEvent_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (coordinate : CountCoordinate mdp)
    (coordinateDelta : Real) (hdelta : 0 < coordinateDelta)
    (hdelta_le_one : coordinateDelta ≤ 1) :
    (policy.iidEpisodeBatchMeasure initialState episodes)
        (coordinate.badEvent policy initialState episodes coordinateDelta) ≤
      ENNReal.ofReal coordinateDelta := by
  cases coordinate with
  | visit stage state action =>
      simpa [CountCoordinate.badEvent, CountCoordinate.deviation] using
        policy.iidEpisodeBatch_visitCount_abs_tail_le
          initialState episodes hepisodes stage state action
          coordinateDelta hdelta hdelta_le_one
  | transition stage state action nextState =>
      simpa [CountCoordinate.badEvent, CountCoordinate.deviation] using
        policy.iidEpisodeBatch_transitionCount_abs_tail_le
          initialState episodes hepisodes stage state action nextState
          coordinateDelta hdelta hdelta_le_one

/-- Union of every visit and joint-transition count bad event. -/
noncomputable def simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta : Real) : Set (EpisodeBatch mdp episodes) :=
  ⋃ coordinate : CountCoordinate mdp,
    coordinate.badEvent policy initialState episodes
      (simultaneousCountDelta mdp delta)

omit [Nonempty State] [Nonempty Action] in
/-- The simultaneous count bad event is measurable. -/
theorem measurableSet_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta : Real) :
    MeasurableSet (policy.simultaneousCountBadEvent initialState episodes delta) := by
  unfold simultaneousCountBadEvent
  exact MeasurableSet.iUnion fun coordinate =>
    coordinate.measurableSet_badEvent policy initialState episodes
      (simultaneousCountDelta mdp delta)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A nonempty coordinate family receives a positive equal delta share. -/
theorem simultaneousCountDelta_pos
    {mdp : MDP State Action} (hcoordinate : Nonempty (CountCoordinate mdp))
    {delta : Real} (hdelta : 0 < delta) :
    0 < simultaneousCountDelta mdp delta := by
  unfold simultaneousCountDelta countCoordinateCard
  exact div_pos hdelta (by
    exact_mod_cast Fintype.card_pos_iff.mpr hcoordinate)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A global delta at most one gives every nonempty-family share at most one. -/
theorem simultaneousCountDelta_le_one
    {mdp : MDP State Action} (hcoordinate : Nonempty (CountCoordinate mdp))
    {delta : Real} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    simultaneousCountDelta mdp delta ≤ 1 := by
  have hcardNat : 0 < Fintype.card (CountCoordinate mdp) :=
    Fintype.card_pos_iff.mpr hcoordinate
  have hcardReal : (1 : Real) ≤ Fintype.card (CountCoordinate mdp) := by
    exact_mod_cast hcardNat
  exact (div_le_self (le_of_lt hdelta) hcardReal).trans hdelta_le_one

omit [Nonempty State] [Nonempty Action] in
/--
All finite visit and joint-transition count deviations share one global delta
budget. When the coordinate family is empty (in particular at horizon zero),
the bad union is empty and no positive-horizon premise is needed.
-/
theorem iidEpisodeBatch_simultaneousCountBadEvent_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    (policy.iidEpisodeBatchMeasure initialState episodes)
        (policy.simultaneousCountBadEvent initialState episodes delta) ≤
      ENNReal.ofReal delta := by
  classical
  by_cases hcoordinate : Nonempty (CountCoordinate mdp)
  · letI : Nonempty (CountCoordinate mdp) := hcoordinate
    have htail : ∀ coordinate : CountCoordinate mdp,
        coordinate ∈ (Finset.univ : Finset (CountCoordinate mdp)) →
          (policy.iidEpisodeBatchMeasure initialState episodes)
              (coordinate.badEvent policy initialState episodes
                (simultaneousCountDelta mdp delta)) ≤
            ENNReal.ofReal
              (delta / ((Finset.univ : Finset (CountCoordinate mdp)).card : Real)) := by
      intro coordinate _hcoordinate
      simpa [simultaneousCountDelta, countCoordinateCard] using
        policy.measure_countCoordinate_badEvent_le
          initialState episodes hepisodes coordinate
          (simultaneousCountDelta mdp delta)
          (simultaneousCountDelta_pos hcoordinate hdelta)
          (simultaneousCountDelta_le_one
            hcoordinate hdelta hdelta_le_one)
    simpa [simultaneousCountBadEvent] using
      (ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
        (policy.iidEpisodeBatchMeasure initialState episodes)
        (Finset.univ : Finset (CountCoordinate mdp))
        Finset.univ_nonempty delta
        (fun coordinate => coordinate.badEvent policy initialState episodes
          (simultaneousCountDelta mdp delta))
        htail)
  · have hcard : Fintype.card (CountCoordinate mdp) = 0 :=
      Nat.eq_zero_of_not_pos fun hpos =>
        hcoordinate (Fintype.card_pos_iff.mp hpos)
    letI : IsEmpty (CountCoordinate mdp) := Fintype.card_eq_zero_iff.mp hcard
    simp [simultaneousCountBadEvent]

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Outside the simultaneous union, every indexed deviation is below its radius. -/
theorem countCoordinate_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉ policy.simultaneousCountBadEvent initialState episodes delta)
    (coordinate : CountCoordinate mdp) :
    |coordinate.deviation policy initialState batch| <
      simultaneousCountConfidenceRadius mdp episodes delta := by
  have hnot : batch ∉ coordinate.badEvent policy initialState episodes
      (simultaneousCountDelta mdp delta) := by
    intro hmem
    apply hbatch
    exact Set.mem_iUnion.2 ⟨coordinate, hmem⟩
  exact lt_of_not_ge (by
    simpa [CountCoordinate.badEvent, simultaneousCountConfidenceRadius] using hnot)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Visit-count specialization of the simultaneous good-side bound. -/
theorem visitCount_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉ policy.simultaneousCountBadEvent initialState episodes delta)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    |(batch.visitCount stage state action : Real) -
        (episodes : Real) *
          policy.stageVisitProbability initialState stage state action| <
      simultaneousCountConfidenceRadius mdp episodes delta := by
  simpa [CountCoordinate.deviation] using
    policy.countCoordinate_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch (CountCoordinate.visit stage state action)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Joint-transition-count specialization of the simultaneous good-side bound. -/
theorem transitionCount_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉ policy.simultaneousCountBadEvent initialState episodes delta)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    |(batch.transitionCount stage state action nextState : Real) -
        (episodes : Real) *
          policy.stageTransitionJointProbability initialState stage state action nextState| <
      simultaneousCountConfidenceRadius mdp episodes delta := by
  simpa [CountCoordinate.deviation] using
    policy.countCoordinate_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch
      (CountCoordinate.transition stage state action nextState)

omit [Nonempty State] [Nonempty Action] in
/--
Route endpoint: one global-delta bad union and all coordinatewise good-side
bounds under the same mapped fixed-policy iid episode-batch law.
-/
theorem iidEpisodeBatch_simultaneous_count_confidence
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    (policy.iidEpisodeBatchMeasure initialState episodes)
        (policy.simultaneousCountBadEvent initialState episodes delta) ≤
        ENNReal.ofReal delta ∧
      ∀ batch ∉ policy.simultaneousCountBadEvent initialState episodes delta,
        ∀ coordinate : CountCoordinate mdp,
          |coordinate.deviation policy initialState batch| <
            simultaneousCountConfidenceRadius mdp episodes delta := by
  refine ⟨policy.iidEpisodeBatch_simultaneousCountBadEvent_le
    initialState episodes hepisodes delta hdelta hdelta_le_one, ?_⟩
  intro batch hbatch coordinate
  exact policy.countCoordinate_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
    initialState batch hbatch coordinate

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
