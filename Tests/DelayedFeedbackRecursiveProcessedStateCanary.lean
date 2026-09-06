import BanditRLProof.DelayedFeedback.RecursiveProcessedState

open BanditRLProof

namespace BanditRLProof.DelayedFeedback

/-- Two processed source rounds deliberately listed out of chronological
order.  The example guards against silently identifying processing order with
source-round order. -/
def nonchronologicalTwoArmTraceSummary : DelayedSAPOProcessedTraceSummary 2 where
  length := 2
  sourceIndex := fun q => if q.1 = 0 then 3 else 1
  sourceIndex_injective := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  currentActionRound := 4
  delayAt := fun _ => 0
  source_available := by
    intro q
    split <;> omega
  activeAtSourceRound := fun _ => Finset.univ
  sourceActive_antitone := by
    intro _s _t _hst
    exact Finset.Subset.rfl
  currentActive := Finset.univ
  currentActive_subset_sourceActive := by
    intro _q
    exact Finset.Subset.rfl
  chosenArmAt := fun t =>
    ⟨t % 2, Nat.mod_lt _ (by norm_num)⟩
  inactiveProbabilityAt := fun _ _ => 0
  empiricalMean := fun _ => 0
  importanceUpper := fun _ => 1
  previousEmpiricalUpper := fun _ => 1
  ucbStar := 1

example : nonchronologicalTwoArmTraceSummary.sourceIndex ⟨0, by
    change 0 < 2
    norm_num⟩ = 3 := by
  rfl

example : nonchronologicalTwoArmTraceSummary.sourceIndex ⟨1, by
    change 1 < 2
    norm_num⟩ = 1 := by
  rfl

example :
    nonchronologicalTwoArmTraceSummary.sourceIndex ⟨1, by
      change 1 < 2
      norm_num⟩ <
      nonchronologicalTwoArmTraceSummary.sourceIndex ⟨0, by
        change 0 < 2
        norm_num⟩ := by
  change 1 < 3
  norm_num

/-- The source-time chosen action is read through the explicit source index,
not through the ledger position. -/
example (q : Fin nonchronologicalTwoArmTraceSummary.length) :
    nonchronologicalTwoArmTraceSummary.toProcessedPrefix.chosenArmAtSource q =
      nonchronologicalTwoArmTraceSummary.chosenArmAt
        (nonchronologicalTwoArmTraceSummary.sourceIndex q) := by
  rfl

/-- Likewise the source-time allocation used by expected pull mass is read
from the recorded source index. -/
example (q : Fin nonchronologicalTwoArmTraceSummary.length) (i : Fin 2) :
    nonchronologicalTwoArmTraceSummary.toProcessedPrefix.activeAtSource q =
        nonchronologicalTwoArmTraceSummary.activeAtSourceRound
          (nonchronologicalTwoArmTraceSummary.sourceIndex q) /\
      nonchronologicalTwoArmTraceSummary.toProcessedPrefix.inactiveProbabilityAtSource
          q i =
        nonchronologicalTwoArmTraceSummary.inactiveProbabilityAt
          (nonchronologicalTwoArmTraceSummary.sourceIndex q) i := by
  exact ⟨rfl, rfl⟩

/-- Current activity persists backwards to every possibly nonchronological
source entry by the explicit trace-summary invariant; source-trace antitonicity
is recorded separately. -/
example (q : Fin nonchronologicalTwoArmTraceSummary.length) :
    (nonchronologicalTwoArmTraceSummary.toConfidenceSnapshot 4).active <=
      nonchronologicalTwoArmTraceSummary.toProcessedPrefix.activeAtSource q := by
  simpa [DelayedSAPOProcessedTraceSummary.toConfidenceSnapshot,
    DelayedSAPOProcessedTraceSummary.toProcessedPrefix] using
      nonchronologicalTwoArmTraceSummary.currentActive_subset_activeAt_sourceIndex q

#check DelayedSAPOProcessedTraceSummary.D4CountClause
#check DelayedSAPOProcessedTraceSummary.toProcessedPrefixCountCertificate
#check DelayedSAPOProcessedTraceSummary.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_traceSummary

#print axioms DelayedSAPOProcessedTraceSummary.currentActive_subset_activeAt_sourceIndex
#print axioms DelayedSAPOProcessedTraceSummary.toProcessedPrefixCountCertificate
#print axioms DelayedSAPOProcessedTraceSummary.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_traceSummary

end BanditRLProof.DelayedFeedback
