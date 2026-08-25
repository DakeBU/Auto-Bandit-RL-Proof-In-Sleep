import BanditRLProof.DelayedFeedback.OrderedProcessingTransition

open BanditRLProof

namespace BanditRLProof.DelayedFeedback

/-- A source-faithful within-round structural state after source round three
has been processed first.  Source rounds one and three both become available
at action round four because `1 + 2 = 3 + 0 = 3`. -/
def orderedProcessingTwoArmState : DelayedSAPOStructuralRoundState 2 where
  currentActionRound := 4
  currentActionRound_pos := by norm_num
  delayAt := fun s => if s = 1 then 2 else 0
  processedOrder := [3]
  processedOrder_nodup := by simp
  processedOrder_available := by
    intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    subst s
    norm_num
  activeAtSourceRound := fun _ => Finset.univ
  sourceActive_antitone := by
    intro _s _t _hst
    exact Finset.Subset.rfl
  currentActive := Finset.univ
  currentActive_subset_roundStart := Finset.Subset.rfl
  chosenArmAt := fun t =>
    ⟨t % 2, Nat.mod_lt _ (by norm_num)⟩
  inactiveProbabilityAt := fun _ _ => 0

/-- The source permits processing source round one after source round three
within their common arrival batch; the inner-loop order is deliberately not
chronological. -/
def nonchronologicalNoSwitchStep :
    DelayedSAPONoSwitchProcessOne orderedProcessingTwoArmState where
  sourceRound := 1
  source_new := by
    native_decide
  empiricalMean := fun _ => 0
  importanceUpper := fun _ => 1
  previousEmpiricalUpper := fun _ => 1
  ucbStar := 1

example : nonchronologicalNoSwitchStep.extendedOrder = [3, 1] := by
  rfl

example : nonchronologicalNoSwitchStep.extendedOrder.Nodup :=
  nonchronologicalNoSwitchStep.extendedOrder_nodup

example :
    nonchronologicalNoSwitchStep.toPreEliminationSummary.sourceIndex
      ⟨0, by
        change 0 < ([3, 1] : List Nat).length
        decide⟩ = 3 := by
  rfl

example :
    nonchronologicalNoSwitchStep.toPreEliminationSummary.sourceIndex
      ⟨1, by
        change 1 < ([3, 1] : List Nat).length
        decide⟩ = 1 := by
  rfl

example (q : Fin nonchronologicalNoSwitchStep.toPreEliminationSummary.length) :
    nonchronologicalNoSwitchStep.toPreEliminationSummary.currentActive <=
      nonchronologicalNoSwitchStep.toPreEliminationSummary.activeAtSourceRound
        (nonchronologicalNoSwitchStep.toPreEliminationSummary.sourceIndex q) :=
  nonchronologicalNoSwitchStep.toPreEliminationSummary.currentActive_subset_sourceActive q

example (q : Fin nonchronologicalNoSwitchStep.toPreEliminationSummary.length) :
    nonchronologicalNoSwitchStep.toPreEliminationSummary.sourceIndex q +
        nonchronologicalNoSwitchStep.toPreEliminationSummary.delayAt
          (nonchronologicalNoSwitchStep.toPreEliminationSummary.sourceIndex q) <
      nonchronologicalNoSwitchStep.toPreEliminationSummary.currentActionRound :=
  nonchronologicalNoSwitchStep.toPreEliminationSummary.source_available q

example :
    (nonchronologicalNoSwitchStep.afterLine8 4).processedOrder = [3, 1] := by
  rfl

example :
    (nonchronologicalNoSwitchStep.afterLine8 4).currentActive =
      (nonchronologicalNoSwitchStep.toPreEliminationSummary.toConfidenceSnapshot 4).remainingActive := by
  rfl

example :
    (nonchronologicalNoSwitchStep.afterLine8 4).currentActive <=
      orderedProcessingTwoArmState.currentActive :=
  nonchronologicalNoSwitchStep.afterLine8_currentActive_subset_before 4

example :
    (nonchronologicalNoSwitchStep.afterLine8 4).currentActive <=
      orderedProcessingTwoArmState.activeAtSourceRound
        (orderedProcessingTwoArmState.currentActionRound - 1) :=
  nonchronologicalNoSwitchStep.afterLine8_preserves_roundStart 4

#check DelayedSAPOStructuralRoundState.currentActive_subset_activeAtSourceRound
#check DelayedSAPONoSwitchProcessOne.toPreEliminationSummary
#check DelayedSAPONoSwitchProcessOne.afterLine8
#check DelayedSAPONoSwitchProcessOne.afterLine8_currentActive_subset_before
#check DelayedSAPONoSwitchProcessOne.afterLine8_preserves_roundStart

#print axioms DelayedSAPOStructuralRoundState.currentActive_subset_activeAtSourceRound
#print axioms DelayedSAPONoSwitchProcessOne.extendedOrder_nodup
#print axioms DelayedSAPONoSwitchProcessOne.toPreEliminationSummary
#print axioms DelayedSAPONoSwitchProcessOne.afterLine8_currentActive_subset_before
#print axioms DelayedSAPONoSwitchProcessOne.afterLine8_preserves_roundStart

end BanditRLProof.DelayedFeedback
