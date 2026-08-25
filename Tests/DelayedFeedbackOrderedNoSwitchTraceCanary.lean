import BanditRLProof.DelayedFeedback.OrderedNoSwitchTrace

open BanditRLProof

namespace BanditRLProof.DelayedFeedback

/-- A completed first action round: with zero delay, source round zero is the
only feedback available before action round one and has already been
processed. -/
def orderedTraceRoundOneState : DelayedSAPOStructuralRoundState 2 where
  currentActionRound := 1
  currentActionRound_pos := by norm_num
  delayAt := fun _ => 0
  processedOrder := [0]
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

def orderedTraceRoundOneClose :
    DelayedSAPONoSwitchRoundClose orderedTraceRoundOneState where
  noNew := by native_decide
  currentActive_eq_sourceRound := rfl

example :
    orderedTraceRoundOneState.processedOrder.toFinset =
      observedBefore orderedTraceRoundOneState.delayAt
        orderedTraceRoundOneState.currentActionRound :=
  orderedTraceRoundOneClose.processedOrder_toFinset_eq_observedBefore

example : orderedTraceRoundOneClose.nextRoundState.currentActionRound = 2 := by
  rfl

/-- At the next action round, source round one is the unique new item and can
be processed by the exact one-step transition. -/
noncomputable def orderedTraceRoundTwoStep :
    DelayedSAPONoSwitchProcessOne orderedTraceRoundOneClose.nextRoundState where
  sourceRound := 1
  source_new := by native_decide
  empiricalMean := fun i => if i = 0 then 0 else 1
  importanceUpper := fun _ => 1
  previousEmpiricalUpper := fun _ => 1
  ucbStar := 1 / 2

/-- The public canary contains both structural edge kinds: exhausted-round
advance followed by exact line-8 processing. -/
def orderedTraceAdvanceThenProcess :
    DelayedSAPONoSwitchStructuralReachable 4 orderedTraceRoundOneState
      (orderedTraceRoundTwoStep.afterLine8 4) :=
  (Relation.ReflTransGen.single
      (DelayedSAPONoSwitchStructuralStep.nextRound orderedTraceRoundOneClose)).tail
    (DelayedSAPONoSwitchStructuralStep.process orderedTraceRoundTwoStep)

example :
    (orderedTraceRoundTwoStep.afterLine8 4).currentActive <=
      orderedTraceRoundOneState.currentActive :=
  currentActive_subset_of_structuralReachable orderedTraceAdvanceThenProcess

#check DelayedSAPONoSwitchRoundClose.processedOrder_toFinset_eq_observedBefore
#check DelayedSAPONoSwitchRoundClose.nextRoundState
#check DelayedSAPONoSwitchStructuralStep
#check DelayedSAPONoSwitchStructuralReachable
#check currentActive_subset_of_structuralReachable
#check mem_earlierRemainingActive_of_laterEliminated
#check gap_le_twenty_mul_gap_of_ordered_no_switch_eliminations

#print axioms DelayedSAPONoSwitchRoundClose.processedOrder_toFinset_eq_observedBefore
#print axioms currentActive_subset_of_structuralReachable
#print axioms mem_earlierRemainingActive_of_laterEliminated
#print axioms gap_le_twenty_mul_gap_of_ordered_no_switch_eliminations

end BanditRLProof.DelayedFeedback
