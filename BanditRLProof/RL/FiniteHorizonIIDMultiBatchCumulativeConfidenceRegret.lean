import BanditRLProof.RL.FiniteHorizonIIDAllCoordinateFiniteBatchConfidence
import BanditRLProof.ProbabilityUnionBound

/-!
# Finite iid multibatch confidence and cumulative expected regret

This module takes a finite Mathlib product of the compiled fixed-policy iid
episode-batch law. Each product coordinate receives an equal confidence share.
Outside the finite union of pulled-back count events, every batch-specific
empirical model has a confidence witness, and the resulting one-episode
expected-regret bounds sum over the finite product index.

The data-generating policy is fixed across product coordinates. The optimistic
policy may depend on its batch, but this is not an adaptive online trajectory
law and the cumulative quantity is a sum of expected regrets, not realized
cumulative regret.
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
    [Nonempty Action]

/-- Equal confidence share assigned to every product-batch coordinate. -/
noncomputable def multiBatchLocalDelta (rounds : Nat) (delta : Real) : Real :=
  delta / (rounds : Real)

namespace MarkovPolicy

/-- Finite product of one fixed-policy iid episode-batch law. -/
noncomputable def iidEpisodeBatchFamilyMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds episodes : Nat) :
    Measure (Fin rounds -> EpisodeBatch mdp episodes) :=
  Measure.pi fun _round : Fin rounds =>
    policy.iidEpisodeBatchMeasure initialState episodes

omit [DecidableEq State] [DecidableEq Action] [Nonempty Action] in
/-- Every product coordinate has the compiled single-batch marginal law. -/
theorem iidEpisodeBatchFamilyMeasure_map_eval
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds episodes : Nat) (round : Fin rounds) :
    (policy.iidEpisodeBatchFamilyMeasure initialState rounds episodes).map
        (Function.eval round) =
      policy.iidEpisodeBatchMeasure initialState episodes := by
  exact
    (MeasureTheory.measurePreserving_eval
      (fun _round : Fin rounds =>
        policy.iidEpisodeBatchMeasure initialState episodes) round).map_eq

/-- Pullback of one local simultaneous-count event to a product coordinate. -/
def multiBatchRoundBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds episodes : Nat) (delta : Real)
    (round : Fin rounds) :
    Set (Fin rounds -> EpisodeBatch mdp episodes) :=
  (Function.eval round) ⁻¹'
    policy.simultaneousCountBadEvent initialState episodes
      (multiBatchLocalDelta rounds delta)

/-- Union of the local simultaneous-count events over all product batches. -/
def multiBatchSimultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds episodes : Nat) (delta : Real) :
    Set (Fin rounds -> EpisodeBatch mdp episodes) :=
  ⋃ round, policy.multiBatchRoundBadEvent
    initialState rounds episodes delta round

omit [Nonempty Action] in
/-- The pulled-back finite union is measurable. -/
theorem measurableSet_multiBatchSimultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds episodes : Nat) (delta : Real) :
    MeasurableSet
      (policy.multiBatchSimultaneousCountBadEvent
        initialState rounds episodes delta) := by
  unfold multiBatchSimultaneousCountBadEvent multiBatchRoundBadEvent
  exact MeasurableSet.iUnion fun round =>
    (policy.measurableSet_simultaneousCountBadEvent initialState episodes
      (multiBatchLocalDelta rounds delta)).preimage
        (measurable_pi_apply round)

omit [Nonempty Action] in
/-- Each pulled-back local event has its equal-share probability bound. -/
theorem iidEpisodeBatchFamilyMeasure_roundBadEvent_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds : Nat) (hrounds : 0 < rounds)
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (round : Fin rounds) :
    (policy.iidEpisodeBatchFamilyMeasure initialState rounds episodes)
        (policy.multiBatchRoundBadEvent
          initialState rounds episodes delta round) <=
      ENNReal.ofReal (multiBatchLocalDelta rounds delta) := by
  have hroundsReal : 0 < (rounds : Real) := Nat.cast_pos.mpr hrounds
  have hroundsOne : (1 : Real) <= (rounds : Real) := by
    exact_mod_cast hrounds
  have hlocal_pos : 0 < multiBatchLocalDelta rounds delta :=
    div_pos hdelta hroundsReal
  have hlocal_le_one : multiBatchLocalDelta rounds delta <= 1 := by
    unfold multiBatchLocalDelta
    exact (div_le_one hroundsReal).2 (hdelta_le_one.trans hroundsOne)
  let evaluation := MeasureTheory.measurePreserving_eval
    (fun _round : Fin rounds =>
      policy.iidEpisodeBatchMeasure initialState episodes) round
  rw [multiBatchRoundBadEvent]
  unfold iidEpisodeBatchFamilyMeasure
  rw [evaluation.measure_preimage
    (policy.measurableSet_simultaneousCountBadEvent
      initialState episodes (multiBatchLocalDelta rounds delta)).nullMeasurableSet]
  exact policy.iidEpisodeBatch_simultaneousCountBadEvent_le
    initialState episodes hepisodes (multiBatchLocalDelta rounds delta)
      hlocal_pos hlocal_le_one

omit [Nonempty Action] in
/-- Equal-share union over product coordinates retains the global delta. -/
theorem iidEpisodeBatchFamilyMeasure_multiBatchSimultaneousCountBadEvent_le
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds : Nat) (hrounds : 0 < rounds)
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (policy.iidEpisodeBatchFamilyMeasure initialState rounds episodes)
        (policy.multiBatchSimultaneousCountBadEvent
          initialState rounds episodes delta) <=
      ENNReal.ofReal delta := by
  letI : Nonempty (Fin rounds) := ⟨⟨0, hrounds⟩⟩
  simpa [multiBatchSimultaneousCountBadEvent, multiBatchLocalDelta] using
    (ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
      (policy.iidEpisodeBatchFamilyMeasure initialState rounds episodes)
      (Finset.univ : Finset (Fin rounds)) Finset.univ_nonempty delta
      (fun round => policy.multiBatchRoundBadEvent
        initialState rounds episodes delta round)
      (fun round _hround => by
        simpa [multiBatchLocalDelta] using
          policy.iidEpisodeBatchFamilyMeasure_roundBadEvent_le
            initialState rounds hrounds episodes hepisodes delta hdelta
              hdelta_le_one round))

omit [DecidableEq State] [DecidableEq Action] [Nonempty Action] in
/-- Every product batch is reward-consistent almost everywhere. -/
theorem iidEpisodeBatchFamilyMeasure_rewardConsistent_ae
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds episodes : Nat) :
    ∀ᵐ batches ∂policy.iidEpisodeBatchFamilyMeasure
        initialState rounds episodes,
      ∀ round, (batches round).RewardConsistent := by
  rw [ae_all_iff]
  intro round
  have htarget := policy.iidEpisodeBatchMeasure_rewardConsistent_ae
    initialState episodes
  rw [← policy.iidEpisodeBatchFamilyMeasure_map_eval
    initialState rounds episodes round] at htarget
  exact ae_of_ae_map (measurable_pi_apply round).aemeasurable htarget

/-- Batch-specific canonical empirical model at one product coordinate. -/
noncomputable def multiBatchEmpiricalModelAt
    {mdp : MDP State Action} (_policy : MarkovPolicy mdp)
    {rounds episodes : Nat} (batches : Fin rounds -> EpisodeBatch mdp episodes)
    (defaultState : State) (transitionBudget : Real) (round : Fin rounds) :
    MDP.FiniteBatchModel mdp episodes :=
  mdp.allCoordinateEmpiricalFiniteBatchModel episodes (batches round)
    defaultState transitionBudget

/-- Sum of batch-specific optimistic-policy expected regrets. -/
noncomputable def multiBatchCumulativeExpectedRegret
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) {rounds episodes : Nat}
    (batches : Fin rounds -> EpisodeBatch mdp episodes)
    (defaultState : State) (transitionBudget : Real) : Real :=
  ∑ round, (policy.multiBatchEmpiricalModelAt batches defaultState
    transitionBudget round).plan.optimisticPolicy.expectedRegret initialState

/-- Sum of the batch-specific selected-radius occupancy bounds. -/
noncomputable def multiBatchCumulativeSelectedRadiusOccupancy
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) {rounds episodes : Nat}
    (batches : Fin rounds -> EpisodeBatch mdp episodes)
    (defaultState : State) (transitionBudget : Real) : Real :=
  ∑ round,
    let model := policy.multiBatchEmpiricalModelAt batches defaultState
      transitionBudget round
    model.plan.optimisticPolicy.occupancySumRemaining
      (fun remaining hremaining state =>
        2 * model.plan.selectedRadiusRemaining remaining hremaining state)
      mdp.horizon le_rfl initialState

/--
Pathwise confidence-family producer outside the finite pulled-back bad-event
union, assuming the generated reward-consistency support at every coordinate.
-/
noncomputable def allCoordinateConfidenceFamily_of_not_mem
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {rounds episodes : Nat} {delta : Real}
    (batches : Fin rounds -> EpisodeBatch mdp episodes)
    (hbatches : batches ∉ policy.multiBatchSimultaneousCountBadEvent
      initialState rounds episodes delta)
    (hreward : ∀ round, (batches round).RewardConsistent)
    (defaultState : State) (rewardBound transitionBudget : Real)
    (hrewardBound : ∀ state action, |mdp.reward state action| <= rewardBound)
    (htransitionBudget_nonneg : 0 <= transitionBudget)
    (hmargin : ∀ coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes
          (multiBatchLocalDelta rounds delta) <
        coordinate.expectedCount policy initialState episodes)
    (hcover : ∀ (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes (multiBatchLocalDelta rounds delta)
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            empiricalFiniteBatchValueEnvelope
              rewardBound transitionBudget remaining) <=
        transitionBudget) :
    ∀ round,
      (policy.multiBatchEmpiricalModelAt batches defaultState
        transitionBudget round).Confidence := by
  intro round
  have hround : batches round ∉ policy.simultaneousCountBadEvent
      initialState episodes (multiBatchLocalDelta rounds delta) := by
    intro hbad
    apply hbatches
    apply Set.mem_iUnion_of_mem round
    simpa [multiBatchRoundBadEvent] using hbad
  exact policy.allCoordinateEmpiricalFiniteBatchModelConfidence_of_not_mem
    initialState (batches round) hround (hreward round) defaultState
      rewardBound transitionBudget hrewardBound htransitionBudget_nonneg
        hmargin hcover

/-- Finite sums preserve all roundwise optimism and expected-regret bounds. -/
theorem confidenceFamily_optimism_and_cumulativeExpectedRegret
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {rounds episodes : Nat}
    (batches : Fin rounds -> EpisodeBatch mdp episodes)
    (defaultState : State) (transitionBudget : Real)
    (confidence : ∀ round,
      (policy.multiBatchEmpiricalModelAt batches defaultState
        transitionBudget round).Confidence) :
    (∀ round state,
        mdp.optimalValueRemaining mdp.horizon le_rfl state <=
          (policy.multiBatchEmpiricalModelAt batches defaultState
            transitionBudget round).plan.upperValueRemaining
              mdp.horizon le_rfl state) ∧
      policy.multiBatchCumulativeExpectedRegret initialState batches
          defaultState transitionBudget <=
        policy.multiBatchCumulativeSelectedRadiusOccupancy initialState batches
          defaultState transitionBudget := by
  constructor
  · intro round state
    exact
      (MDP.FiniteBatchModel.Confidence.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
          (confidence round) initialState).1 state
  · unfold multiBatchCumulativeExpectedRegret
      multiBatchCumulativeSelectedRadiusOccupancy
    apply Finset.sum_le_sum
    intro round _hround
    exact
      (MDP.FiniteBatchModel.Confidence.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
          (confidence round) initialState).2

/--
Mapped finite-product confidence endpoint: one global-delta event and an a.e.
family of confidence witnesses, with no measurable witness selection claim.
-/
theorem iidEpisodeBatchFamily_allCoordinate_finiteBatchModel_confidence
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds : Nat) (hrounds : 0 < rounds)
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (defaultState : State) (rewardBound transitionBudget : Real)
    (hrewardBound : ∀ state action, |mdp.reward state action| <= rewardBound)
    (htransitionBudget_nonneg : 0 <= transitionBudget)
    (hmargin : ∀ coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes
          (multiBatchLocalDelta rounds delta) <
        coordinate.expectedCount policy initialState episodes)
    (hcover : ∀ (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes (multiBatchLocalDelta rounds delta)
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            empiricalFiniteBatchValueEnvelope
              rewardBound transitionBudget remaining) <=
        transitionBudget) :
    MeasurableSet (policy.multiBatchSimultaneousCountBadEvent
        initialState rounds episodes delta) ∧
      (policy.iidEpisodeBatchFamilyMeasure initialState rounds episodes)
          (policy.multiBatchSimultaneousCountBadEvent
            initialState rounds episodes delta) <=
        ENNReal.ofReal delta ∧
      ∀ᵐ batches ∂policy.iidEpisodeBatchFamilyMeasure
          initialState rounds episodes,
        batches ∉ policy.multiBatchSimultaneousCountBadEvent
            initialState rounds episodes delta ->
          Nonempty (∀ round,
            (policy.multiBatchEmpiricalModelAt batches defaultState
              transitionBudget round).Confidence) := by
  refine ⟨policy.measurableSet_multiBatchSimultaneousCountBadEvent
      initialState rounds episodes delta,
    policy.iidEpisodeBatchFamilyMeasure_multiBatchSimultaneousCountBadEvent_le
      initialState rounds hrounds episodes hepisodes delta hdelta
        hdelta_le_one, ?_⟩
  filter_upwards [policy.iidEpisodeBatchFamilyMeasure_rewardConsistent_ae
    initialState rounds episodes] with batches hreward
  intro hbatches
  exact ⟨policy.allCoordinateConfidenceFamily_of_not_mem
    initialState batches hbatches hreward defaultState rewardBound
      transitionBudget hrewardBound htransitionBudget_nonneg hmargin hcover⟩

/--
Route endpoint: the same finite-product event simultaneously yields optimism
for every batch model and the cumulative finite sum of expected-regret bounds.
-/
theorem iidEpisodeBatchFamily_allCoordinate_optimism_and_cumulativeExpectedRegret
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (rounds : Nat) (hrounds : 0 < rounds)
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (defaultState : State) (rewardBound transitionBudget : Real)
    (hrewardBound : ∀ state action, |mdp.reward state action| <= rewardBound)
    (htransitionBudget_nonneg : 0 <= transitionBudget)
    (hmargin : ∀ coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes
          (multiBatchLocalDelta rounds delta) <
        coordinate.expectedCount policy initialState episodes)
    (hcover : ∀ (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes (multiBatchLocalDelta rounds delta)
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            empiricalFiniteBatchValueEnvelope
              rewardBound transitionBudget remaining) <=
        transitionBudget) :
    MeasurableSet (policy.multiBatchSimultaneousCountBadEvent
        initialState rounds episodes delta) ∧
      (policy.iidEpisodeBatchFamilyMeasure initialState rounds episodes)
          (policy.multiBatchSimultaneousCountBadEvent
            initialState rounds episodes delta) <=
        ENNReal.ofReal delta ∧
      ∀ᵐ batches ∂policy.iidEpisodeBatchFamilyMeasure
          initialState rounds episodes,
        batches ∉ policy.multiBatchSimultaneousCountBadEvent
            initialState rounds episodes delta ->
          (∀ round state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state <=
                (policy.multiBatchEmpiricalModelAt batches defaultState
                  transitionBudget round).plan.upperValueRemaining
                    mdp.horizon le_rfl state) ∧
            policy.multiBatchCumulativeExpectedRegret initialState batches
                defaultState transitionBudget <=
              policy.multiBatchCumulativeSelectedRadiusOccupancy initialState
                batches defaultState transitionBudget := by
  obtain ⟨hmeasurable, htail, hconfidence⟩ :=
    policy.iidEpisodeBatchFamily_allCoordinate_finiteBatchModel_confidence
      initialState rounds hrounds episodes hepisodes delta hdelta hdelta_le_one
        defaultState rewardBound transitionBudget hrewardBound
          htransitionBudget_nonneg hmargin hcover
  refine ⟨hmeasurable, htail, ?_⟩
  filter_upwards [hconfidence] with batches hbatchConfidence
  intro hbatches
  obtain ⟨confidence⟩ := hbatchConfidence hbatches
  exact policy.confidenceFamily_optimism_and_cumulativeExpectedRegret
    initialState batches defaultState transitionBudget confidence

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
