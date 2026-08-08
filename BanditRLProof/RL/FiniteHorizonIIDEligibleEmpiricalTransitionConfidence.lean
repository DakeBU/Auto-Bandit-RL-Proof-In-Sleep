import BanditRLProof.RL.FiniteHorizonEmpiricalModel
import BanditRLProof.RL.FiniteHorizonIIDEligibleVisitCountPositivity
import BanditRLProof.RL.FiniteHorizonStageTransitionJointFactorization

/-!
# Eligible empirical transition confidence for finite-horizon iid batches

This module combines the compiled simultaneous visit/joint-count event,
eligible positive denominators, and generated population-law factorization.
For every eligible state-action-stage coordinate, the empirical singleton
transition mass is within `2 * countRadius / visitCount` of the true transition
kernel singleton mass. The bundled endpoint reuses the existing global-delta
event; it does not spend another failure budget or add reward confidence.
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

namespace MarkovPolicy

omit [Nonempty State] [Nonempty Action] in
/-- A single eligible coordinate inherits a strict empirical transition-mass
bound from the simultaneous visit and joint-transition count deviations. -/
theorem empiricalTransitionMass_abs_sub_transition_lt_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (defaultState : State) (coordinate : VisitCoordinate mdp)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      coordinate.expectedCount policy initialState episodes)
    (nextState : State) :
    |batch.empiricalTransitionMass defaultState coordinate.stage
          coordinate.state coordinate.action nextState -
        (mdp.transition (coordinate.state, coordinate.action)).real {nextState}| <
      2 * simultaneousCountConfidenceRadius mdp episodes delta /
        (coordinate.count batch : Real) := by
  let visit : Real := coordinate.count batch
  let joint : Real :=
    batch.transitionCount coordinate.stage coordinate.state
      coordinate.action nextState
  let expectedVisit : Real :=
    coordinate.expectedCount policy initialState episodes
  let trueMass : Real :=
    (mdp.transition (coordinate.state, coordinate.action)).real {nextState}
  let radius : Real := simultaneousCountConfidenceRadius mdp episodes delta

  have hcountNat : 0 < coordinate.count batch :=
    policy.visitCoordinate_count_pos_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch coordinate hmargin
  have hvisit : 0 < visit := by
    dsimp [visit]
    exact_mod_cast hcountNat
  have hvisitNe :
      batch.visitCount coordinate.stage coordinate.state coordinate.action ≠ 0 := by
    simpa [VisitCoordinate.count] using Nat.ne_of_gt hcountNat
  have hradius : 0 ≤ radius := by
    exact Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hmassNonneg : 0 ≤ trueMass := by
    exact MeasureTheory.measureReal_nonneg
  have hmassLeOne : trueMass ≤ 1 := by
    exact MeasureTheory.measureReal_le_one

  have hvisitDeviation : |visit - expectedVisit| < radius := by
    simpa [visit, expectedVisit, radius, VisitCoordinate.count,
      VisitCoordinate.expectedCount] using
      policy.visitCount_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
        initialState batch hbatch coordinate.stage coordinate.state
          coordinate.action
  have hjointDeviation : |joint - expectedVisit * trueMass| < radius := by
    have hdeviation :=
      policy.transitionCount_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
        initialState batch hbatch coordinate.stage coordinate.state
          coordinate.action nextState
    rw [policy.stageTransitionJointProbability_eq_stageVisitProbability_mul_transition]
      at hdeviation
    simpa [joint, expectedVisit, trueMass, radius,
      VisitCoordinate.expectedCount, Measure.real, mul_assoc] using hdeviation

  have hnumerator : |joint - visit * trueMass| < 2 * radius := by
    calc
      |joint - visit * trueMass| =
          |(joint - expectedVisit * trueMass) -
            trueMass * (visit - expectedVisit)| := by
              congr 1
              ring
      _ ≤ |joint - expectedVisit * trueMass| +
          |trueMass * (visit - expectedVisit)| := abs_sub _ _
      _ = |joint - expectedVisit * trueMass| +
          trueMass * |visit - expectedVisit| := by
            rw [abs_mul, abs_of_nonneg hmassNonneg]
      _ < radius + trueMass * radius :=
        add_lt_add_of_lt_of_le hjointDeviation
          (mul_le_mul_of_nonneg_left (le_of_lt hvisitDeviation) hmassNonneg)
      _ ≤ 2 * radius := by nlinarith

  rw [batch.empiricalTransitionMass_eq_div_of_visitCount_ne_zero
    defaultState coordinate.stage coordinate.state coordinate.action nextState
      hvisitNe]
  change |joint / visit - trueMass| < 2 * radius / visit
  rw [show joint / visit - trueMass =
      (joint - visit * trueMass) / visit by field_simp]
  rw [abs_div, abs_of_pos hvisit]
  exact (div_lt_div_iff_of_pos_right hvisit).2 hnumerator

omit [Nonempty State] [Nonempty Action] in
/--
Route endpoint: the existing measurable simultaneous-count event has global
delta mass, and outside it all eligible empirical transition singleton masses
obey the positive-random-denominator confidence bound simultaneously.
-/
theorem iidEpisodeBatch_eligible_empiricalTransitionMass_confidence
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (defaultState : State) (eligible : Finset (VisitCoordinate mdp))
    (hmargin : ∀ coordinate ∈ eligible,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes) :
    MeasurableSet
        (policy.simultaneousCountBadEvent initialState episodes delta) ∧
      (policy.iidEpisodeBatchMeasure initialState episodes)
          (policy.simultaneousCountBadEvent initialState episodes delta) ≤
        ENNReal.ofReal delta ∧
      ∀ batch ∉ policy.simultaneousCountBadEvent initialState episodes delta,
        ∀ coordinate ∈ eligible, ∀ nextState,
          |batch.empiricalTransitionMass defaultState coordinate.stage
                coordinate.state coordinate.action nextState -
              (mdp.transition
                (coordinate.state, coordinate.action)).real {nextState}| <
            2 * simultaneousCountConfidenceRadius mdp episodes delta /
              (coordinate.count batch : Real) := by
  refine ⟨policy.measurableSet_simultaneousCountBadEvent
      initialState episodes delta,
    policy.iidEpisodeBatch_simultaneousCountBadEvent_le
      initialState episodes hepisodes delta hdelta hdelta_le_one, ?_⟩
  intro batch hbatch coordinate hcoordinate nextState
  exact policy.empiricalTransitionMass_abs_sub_transition_lt_of_not_mem_simultaneousCountBadEvent
    initialState batch hbatch defaultState coordinate
      (hmargin coordinate hcoordinate) nextState

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
