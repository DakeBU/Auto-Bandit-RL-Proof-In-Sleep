import Mathlib.Logic.Relation
import BanditRLProof.DelayedFeedback.OrderedProcessingTransition

/-!
# Ordered no-switch structural traces for Delayed SAPO

This module composes the source-faithful one-item transition from
`OrderedProcessingTransition.lean` across an arbitrary finite trace.  A trace
may either process one member of `B(t) \ S` through the no-switch structural
projection of Algorithm 5 lines 3--4 and 7--8, or close an exhausted inner
loop and advance to the next action round.

The resulting active-set monotonicity discharges one genuine temporal premise
of the repaired D.12 / main-text Lemma-4.2 consumer: an arm eliminated later
must still belong to the earlier line-8 remaining set.  The factor-20 theorem
below remains conditional on the earlier snapshot's D.4 count clause and
elimination-good projection.  No numerical BSC/EAP producer, generated
probability law, D.4 probability bound, switch path, or regret endpoint is
constructed here.
-/

namespace BanditRLProof

namespace DelayedFeedback

/-- Certificate that the no-switch inner loop for one action round is
exhausted and that its final intra-round active set is the line-15 active set
recorded by the source-round trace.

The second field is a structural consistency contract.  It is not a claim
that EAP has already constructed a valid probability vector. -/
structure DelayedSAPONoSwitchRoundClose {K : Nat}
    (state : DelayedSAPOStructuralRoundState K) : Prop where
  noNew :
    newlyObservedBefore state.delayAt state.processedOrder.toFinset
      state.currentActionRound = ∅
  currentActive_eq_sourceRound :
    state.currentActive =
      state.activeAtSourceRound state.currentActionRound

namespace DelayedSAPONoSwitchRoundClose

/-- Exhausting `B(t) \ S` means that the ordered ledger contains exactly the
feedback available before action `t`.  The equality is set-level only and does
not impose a chronological order on simultaneous arrivals. -/
theorem processedOrder_toFinset_eq_observedBefore {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (closed : DelayedSAPONoSwitchRoundClose state) :
    state.processedOrder.toFinset =
      observedBefore state.delayAt state.currentActionRound := by
  apply Finset.Subset.antisymm
  · intro s hs
    have hsList : s ∈ state.processedOrder := by
      simpa using hs
    have havailable := state.processedOrder_available s hsList
    rw [observedBefore, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), havailable⟩
  · intro s hs
    by_contra hprocessed
    have hnew :
        s ∈ newlyObservedBefore state.delayAt
          state.processedOrder.toFinset state.currentActionRound := by
      exact Finset.mem_sdiff.mpr ⟨hs, hprocessed⟩
    rw [closed.noNew] at hnew
    simp at hnew

/-- Structural state at the start of the next action round.  The processed
ledger and active set are unchanged; the round-start invariant follows from
the close certificate's identification with the just-finished source-round
active set. -/
def nextRoundState {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (closed : DelayedSAPONoSwitchRoundClose state) :
    DelayedSAPOStructuralRoundState K where
  currentActionRound := state.currentActionRound + 1
  currentActionRound_pos := Nat.succ_pos state.currentActionRound
  delayAt := state.delayAt
  processedOrder := state.processedOrder
  processedOrder_nodup := state.processedOrder_nodup
  processedOrder_available := by
    intro s hs
    exact lt_trans (state.processedOrder_available s hs)
      (Nat.lt_succ_self state.currentActionRound)
  activeAtSourceRound := state.activeAtSourceRound
  sourceActive_antitone := state.sourceActive_antitone
  currentActive := state.currentActive
  currentActive_subset_roundStart := by
    have hsource :
        state.currentActive <=
          state.activeAtSourceRound state.currentActionRound := by
      rw [closed.currentActive_eq_sourceRound]
    simpa using hsource
  chosenArmAt := state.chosenArmAt
  inactiveProbabilityAt := state.inactiveProbabilityAt

@[simp]
theorem nextRoundState_currentActionRound {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (closed : DelayedSAPONoSwitchRoundClose state) :
    closed.nextRoundState.currentActionRound =
      state.currentActionRound + 1 := rfl

@[simp]
theorem nextRoundState_processedOrder {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (closed : DelayedSAPONoSwitchRoundClose state) :
    closed.nextRoundState.processedOrder = state.processedOrder := rfl

@[simp]
theorem nextRoundState_currentActive {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (closed : DelayedSAPONoSwitchRoundClose state) :
    closed.nextRoundState.currentActive = state.currentActive := rfl

end DelayedSAPONoSwitchRoundClose

/-- One edge of the deterministic no-switch structural trace.  Processing
uses the exact line-8 successor; advancing rounds requires an exhausted-loop
certificate. -/
inductive DelayedSAPONoSwitchStructuralStep {K : Nat}
    (horizon : Nat) :
    DelayedSAPOStructuralRoundState K →
      DelayedSAPOStructuralRoundState K → Prop
  | process {state : DelayedSAPOStructuralRoundState K}
      (step : DelayedSAPONoSwitchProcessOne state) :
      DelayedSAPONoSwitchStructuralStep horizon state
        (step.afterLine8 horizon)
  | nextRound {state : DelayedSAPOStructuralRoundState K}
      (closed : DelayedSAPONoSwitchRoundClose state) :
      DelayedSAPONoSwitchStructuralStep horizon state
        closed.nextRoundState

/-- Finite reflexive-transitive no-switch reachability.  It is a structural
relation, not a generated stochastic trajectory. -/
abbrev DelayedSAPONoSwitchStructuralReachable {K : Nat}
    (horizon : Nat) :=
  Relation.ReflTransGen
    (DelayedSAPONoSwitchStructuralStep (K := K) horizon)

/-- Every primitive no-switch structural edge can only remove arms. -/
theorem currentActive_subset_of_structuralStep {K horizon : Nat}
    {initial final : DelayedSAPOStructuralRoundState K}
    (step :
      DelayedSAPONoSwitchStructuralStep horizon initial final) :
    final.currentActive <= initial.currentActive := by
  cases step with
  | process processStep =>
      exact processStep.afterLine8_currentActive_subset_before horizon
  | nextRound _closed =>
      exact Finset.Subset.rfl

/-- Active sets are antitone along every finite no-switch structural trace. -/
theorem currentActive_subset_of_structuralReachable {K horizon : Nat}
    {initial final : DelayedSAPOStructuralRoundState K}
    (run :
      DelayedSAPONoSwitchStructuralReachable horizon initial final) :
    final.currentActive <= initial.currentActive := by
  induction run using Relation.ReflTransGen.trans_induction_on with
  | refl _state =>
      exact Finset.Subset.rfl
  | single edge =>
      exact currentActive_subset_of_structuralStep edge
  | trans _left _right hleft hright =>
      exact hright.trans hleft

/-- An arm eliminated by a later processing step was still present after an
earlier line-8 removal whenever the two steps are connected by a no-switch
structural trace.  This is the temporal premise previously left to callers. -/
theorem mem_earlierRemainingActive_of_laterEliminated
    {K horizon : Nat}
    {initial laterState : DelayedSAPOStructuralRoundState K}
    (earlierStep : DelayedSAPONoSwitchProcessOne initial)
    (between :
      DelayedSAPONoSwitchStructuralReachable horizon
        (earlierStep.afterLine8 horizon) laterState)
    (laterStep : DelayedSAPONoSwitchProcessOne laterState)
    (iLater : Fin K)
    (hLaterEliminated :
      iLater ∈
        (laterStep.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated) :
    iLater ∈
      (earlierStep.toPreEliminationSummary.toConfidenceSnapshot horizon).remainingActive := by
  have hLaterActive : iLater ∈ laterState.currentActive :=
    (DelayedSAPOEliminationSnapshot.mem_eliminated_iff
      (laterStep.toPreEliminationSummary.toConfidenceSnapshot horizon).toDelayedSAPOEliminationSnapshot
      iLater).mp hLaterEliminated |>.1
  have hEarlierAfter :
      iLater ∈ (earlierStep.afterLine8 horizon).currentActive :=
    currentActive_subset_of_structuralReachable between hLaterActive
  exact hEarlierAfter

/-- Ordered two-elimination factor-20 consumer.  Unlike the one-snapshot
consumer, this theorem derives later-arm survival at the earlier snapshot from
the exact structural trace.  It remains conditional on the earlier D.4 count
clause and elimination-good projection. -/
theorem gap_le_twenty_mul_gap_of_ordered_no_switch_eliminations
    {K : Nat} [Nonempty (Fin K)]
    {initial laterState : DelayedSAPOStructuralRoundState K}
    (horizon : Nat) (hhorizon : 1 < horizon)
    (earlierStep : DelayedSAPONoSwitchProcessOne initial)
    (between :
      DelayedSAPONoSwitchStructuralReachable horizon
        (earlierStep.afterLine8 horizon) laterState)
    (laterStep : DelayedSAPONoSwitchProcessOne laterState)
    (mean : Fin K → Real) (optimal iEarlier iLater : Fin K)
    (hoptimal : ∀ i, mean optimal <= mean i)
    (hmeanBounds : ∀ i, mean i ∈ Set.Icc (0 : Real) 1)
    (hD4 :
      earlierStep.toPreEliminationSummary.D4CountClause horizon)
    (hgood :
      (earlierStep.toPreEliminationSummary.toConfidenceSnapshot horizon).EliminationGoodEvent
        mean)
    (hoptimalActive : optimal ∈ initial.currentActive)
    (hEarlierEliminated :
      iEarlier ∈
        (earlierStep.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated)
    (hLaterEliminated :
      iLater ∈
        (laterStep.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated) :
    mean iLater - mean optimal <=
      20 * (mean iEarlier - mean optimal) := by
  have hLaterRemaining :=
    mem_earlierRemainingActive_of_laterEliminated earlierStep between laterStep
      iLater hLaterEliminated
  exact
    earlierStep.toPreEliminationSummary.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_traceSummary
        horizon hD4 hhorizon mean optimal iEarlier iLater hoptimal hmeanBounds
          hgood hoptimalActive hEarlierEliminated hLaterRemaining

end DelayedFeedback

end BanditRLProof
