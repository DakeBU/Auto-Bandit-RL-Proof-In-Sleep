import BanditRLProof.DelayedFeedback.Processing
import BanditRLProof.DelayedFeedback.RecursiveProcessedState

/-!
# One ordered no-switch processing step for Delayed SAPO

This module formalizes the deterministic structural content of one iteration
of Algorithm 5 lines 3--4 and 7--8.  A newly observed source round is appended
to the paper sequence before the line-7 confidence snapshot is formed.  The
line-8 successor then removes exactly the arms selected by that snapshot.

The source leaves the order of simultaneous arrivals unspecified, so the step
accepts any member of `B(t) \ S` and never sorts by source time.  It models only
the branch on which the line-5 BSC does not switch away from Delayed SAPO.
Numerical confidence surfaces remain explicit structural inputs: this module
does not implement their recursive update, BSC, EAP, a generated trajectory,
the D.4 probability bound, ordered multi-snapshot elimination, or any regret
endpoint.
-/

namespace BanditRLProof

namespace DelayedFeedback

/-- Structural state while Algorithm 5 is processing newly observed feedback
before action `currentActionRound`.

`processedOrder` is the paper sequence `S`, not a sorted set of source rounds.
The current intra-round active set is contained in the previous action round's
line-15 active set.  Together with the antitone source-round trace, this is the
primitive invariant from which a line-7 trace summary obtains current-to-source
active persistence. -/
structure DelayedSAPOStructuralRoundState (K : Nat) where
  currentActionRound : Nat
  currentActionRound_pos : 0 < currentActionRound
  delayAt : Nat -> Nat
  processedOrder : List Nat
  processedOrder_nodup : processedOrder.Nodup
  processedOrder_available : forall s, s ∈ processedOrder ->
    s + delayAt s < currentActionRound
  activeAtSourceRound : Nat -> Finset (Fin K)
  sourceActive_antitone : Antitone activeAtSourceRound
  currentActive : Finset (Fin K)
  currentActive_subset_roundStart :
    currentActive <= activeAtSourceRound (currentActionRound - 1)
  chosenArmAt : Nat -> Fin K
  inactiveProbabilityAt : Nat -> Fin K -> Real

namespace DelayedSAPOStructuralRoundState

/-- Every source already in the processed order lies no later than the action
round immediately preceding the current one. -/
theorem source_le_roundStart {K : Nat}
    (state : DelayedSAPOStructuralRoundState K) {s : Nat}
    (hs : s ∈ state.processedOrder) :
    s <= state.currentActionRound - 1 := by
  have havailable := state.processedOrder_available s hs
  omega

/-- The current intra-round active set is contained in the source-round active
set of every previously processed item. -/
theorem currentActive_subset_activeAtSourceRound {K : Nat}
    (state : DelayedSAPOStructuralRoundState K) {s : Nat}
    (hs : s ∈ state.processedOrder) :
    state.currentActive <= state.activeAtSourceRound s := by
  exact state.currentActive_subset_roundStart.trans
    (state.sourceActive_antitone (state.source_le_roundStart hs))

end DelayedSAPOStructuralRoundState

/-- One source-faithful no-switch iteration of Algorithm 5's inner processing
loop.  `source_new` is exactly line 3's membership in `B(t) \ S`.  The numerical
fields are the values read by line 7 after line 4 has appended `sourceRound`;
constructing them from observed losses is a separate recursive-state leaf. -/
structure DelayedSAPONoSwitchProcessOne {K : Nat}
    (state : DelayedSAPOStructuralRoundState K) where
  sourceRound : Nat
  source_new : sourceRound ∈ newlyObservedBefore state.delayAt
    state.processedOrder.toFinset state.currentActionRound
  empiricalMean : Fin K -> Real
  importanceUpper : Fin K -> Real
  previousEmpiricalUpper : Fin K -> Real
  ucbStar : Real

namespace DelayedSAPONoSwitchProcessOne

/-- Algorithm 5 line 4: append the selected source to the end of the processing
sequence. -/
def extendedOrder {K : Nat} {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) : List Nat :=
  state.processedOrder.concat step.sourceRound

/-- The line-3 source was not already present in the processed sequence. -/
theorem sourceRound_not_mem {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) :
    step.sourceRound ∉ state.processedOrder := by
  have hnotFinset := (Finset.mem_sdiff.mp step.source_new).2
  simpa using hnotFinset

/-- Appending one genuinely new source preserves duplicate freedom. -/
theorem extendedOrder_nodup {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) :
    step.extendedOrder.Nodup := by
  rw [extendedOrder, List.nodup_concat]
  exact ⟨step.sourceRound_not_mem, state.processedOrder_nodup⟩

/-- Every source in the extended sequence satisfies the paper's exact strict
availability condition at the current action round. -/
theorem extendedOrder_available {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) {s : Nat}
    (hs : s ∈ step.extendedOrder) :
    s + state.delayAt s < state.currentActionRound := by
  have hcases : s ∈ state.processedOrder ∨ s = step.sourceRound := by
    simpa [extendedOrder] using hs
  rcases hcases with hold | rfl
  · exact state.processedOrder_available s hold
  · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp step.source_new).1).2

/-- Every source in the extended sequence is at most the previous action
round. -/
theorem extendedSource_le_roundStart {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) {s : Nat}
    (hs : s ∈ step.extendedOrder) :
    s <= state.currentActionRound - 1 := by
  have havailable := step.extendedOrder_available hs
  omega

/-- The line-7 active set is contained in every source-time line-15 active set
represented by the extended processing sequence. -/
theorem currentActive_subset_extendedSourceActive {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) {s : Nat}
    (hs : s ∈ step.extendedOrder) :
    state.currentActive <= state.activeAtSourceRound s := by
  exact state.currentActive_subset_roundStart.trans
    (state.sourceActive_antitone (step.extendedSource_le_roundStart hs))

/-- Line-7 trace summary after, not before, Algorithm 5 line 4 appends the
newly observed source.  Its source-index injectivity, strict availability, and
current-to-source containment are derived from the ordered transition state. -/
def toPreEliminationSummary {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) :
    DelayedSAPOProcessedTraceSummary K where
  length := step.extendedOrder.length
  sourceIndex := step.extendedOrder.get
  sourceIndex_injective := step.extendedOrder_nodup.injective_get
  currentActionRound := state.currentActionRound
  delayAt := state.delayAt
  source_available := by
    intro q
    exact step.extendedOrder_available (List.get_mem step.extendedOrder q)
  activeAtSourceRound := state.activeAtSourceRound
  sourceActive_antitone := state.sourceActive_antitone
  currentActive := state.currentActive
  currentActive_subset_sourceActive := by
    intro q
    exact step.currentActive_subset_extendedSourceActive
      (List.get_mem step.extendedOrder q)
  chosenArmAt := state.chosenArmAt
  inactiveProbabilityAt := state.inactiveProbabilityAt
  empiricalMean := step.empiricalMean
  importanceUpper := step.importanceUpper
  previousEmpiricalUpper := step.previousEmpiricalUpper
  ucbStar := step.ucbStar

/-- The exact Algorithm-5 line-8 removal is contained in the active set read by
the line-7 snapshot. -/
theorem line8RemainingActive_subset_currentActive {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) (horizon : Nat) :
    (step.toPreEliminationSummary.toConfidenceSnapshot horizon).remainingActive <=
      state.currentActive := by
  intro i hi
  have hiActive :
      i ∈ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).active :=
    (DelayedSAPOEliminationSnapshot.mem_remainingActive_iff
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).toDelayedSAPOEliminationSnapshot
      i).mp hi |>.1
  exact hiActive

/-- Algorithm 5 line 8 successor for the same action round.  It preserves the
ordered source sequence and updates only the intra-round active set to the
exact line-7 complement. -/
noncomputable def afterLine8 {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) (horizon : Nat) :
    DelayedSAPOStructuralRoundState K where
  currentActionRound := state.currentActionRound
  currentActionRound_pos := state.currentActionRound_pos
  delayAt := state.delayAt
  processedOrder := step.extendedOrder
  processedOrder_nodup := step.extendedOrder_nodup
  processedOrder_available := by
    intro s hs
    exact step.extendedOrder_available hs
  activeAtSourceRound := state.activeAtSourceRound
  sourceActive_antitone := state.sourceActive_antitone
  currentActive :=
    (step.toPreEliminationSummary.toConfidenceSnapshot horizon).remainingActive
  currentActive_subset_roundStart :=
    (step.line8RemainingActive_subset_currentActive horizon).trans
      state.currentActive_subset_roundStart
  chosenArmAt := state.chosenArmAt
  inactiveProbabilityAt := state.inactiveProbabilityAt

/-- Line 8 can only remove arms from the current intra-round active set. -/
theorem afterLine8_currentActive_subset_before {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) (horizon : Nat) :
    (step.afterLine8 horizon).currentActive <= state.currentActive := by
  exact step.line8RemainingActive_subset_currentActive horizon

/-- The line-8 successor remains below the active set at the start of the
current action round, so another arbitrary new arrival can be processed. -/
theorem afterLine8_preserves_roundStart {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state) (horizon : Nat) :
    (step.afterLine8 horizon).currentActive <=
      state.activeAtSourceRound (state.currentActionRound - 1) := by
  exact (step.afterLine8 horizon).currentActive_subset_roundStart

end DelayedSAPONoSwitchProcessOne

end DelayedFeedback

end BanditRLProof
