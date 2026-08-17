import BanditRLProof.DelayedFeedback.Accounting
import BanditRLProof.DelayedFeedback.ActiveAllocation
import BanditRLProof.DelayedFeedback.CausalView
import BanditRLProof.DelayedFeedback.MultiRegimeContract
import BanditRLProof.DelayedFeedback.Processing

open BanditRLProof

#check DelayedFeedback.observedBefore
#check DelayedFeedback.outstandingAt
#check DelayedFeedback.observedBefore_disjoint_outstandingAt
#check DelayedFeedback.observedBefore_union_outstandingAt
#check DelayedFeedback.card_observedBefore_add_card_outstandingAt
#check DelayedFeedback.outstandingCount
#check DelayedFeedback.maxOutstandingBeforeThrough
#check DelayedFeedback.outstandingCount_le_round
#check DelayedFeedback.outstandingCount_le_maxOutstandingBeforeThrough
#check DelayedFeedback.oneBasedDelayShift
#check DelayedFeedback.paperMissingAtEnd
#check DelayedFeedback.paperMissingAtEnd_eq_outstandingAt_oneBasedDelayShift
#check DelayedFeedback.paperMissingCount
#check DelayedFeedback.paperMissingCount_eq_outstandingCount_oneBasedDelayShift
#check DelayedFeedback.paperMissingCount_le_round
#check DelayedFeedback.paperSigmaMaxThrough
#check DelayedFeedback.paperMissingCount_le_paperSigmaMaxThrough
#check DelayedFeedback.SameAlgorithmMultiRegimeContract
#check DelayedFeedback.SameAlgorithmMultiRegimeContract.stochasticClaim
#check DelayedFeedback.SameAlgorithmMultiRegimeContract.adversarialClaim
#check DelayedFeedback.SameAlgorithmMultiRegimeContract.stochasticClaim_iff_shared_fields
#check DelayedFeedback.SameAlgorithmMultiRegimeContract.adversarialClaim_iff_shared_fields
#check DelayedFeedback.ActionTimeView
#check DelayedFeedback.actionTimeViewAt
#check DelayedFeedback.CausalDecisionRule
#check DelayedFeedback.actionTimeViewAt_outstanding_loss_hidden
#check DelayedFeedback.actionTimeViewAt_eq_of_observation_equivalent
#check DelayedFeedback.causalDecision_eq_of_observation_equivalent
#check DelayedFeedback.newlyObservedBefore
#check DelayedFeedback.observedBefore_mono
#check DelayedFeedback.processed_union_newlyObservedBefore
#check DelayedFeedback.processAllNew
#check DelayedFeedback.processAllNew_from_previous_eq_current
#check DelayedFeedback.outstandingAt_disjoint_newlyObservedBefore
#check DelayedFeedback.inactiveArms
#check DelayedFeedback.activeEqualShare
#check DelayedFeedback.delayedSAPOProbability
#check DelayedFeedback.delayedSAPOProbability_nonneg
#check DelayedFeedback.sum_delayedSAPOProbability_eq_one

def trivialMultiRegimeContract :
    DelayedFeedback.SameAlgorithmMultiRegimeContract
      Unit Unit Unit Unit Unit Unit Unit where
  algorithm := ()
  initialization := ()
  tuning := ()
  information := ()
  comparator := ()
  stochasticEndpoint := fun _ _ _ _ _ _ => True
  adversarialEndpoint := fun _ _ _ _ _ _ => True

example :
    trivialMultiRegimeContract.stochasticClaim () := by
  trivial

example :
    trivialMultiRegimeContract.adversarialClaim () := by
  trivial

example :
    DelayedFeedback.observedBefore (fun _ => 0) 4 = {0, 1, 2, 3} := by
  native_decide

example :
    DelayedFeedback.outstandingAt (fun _ => 0) 4 = ∅ := by
  native_decide

example :
    DelayedFeedback.observedBefore (fun s => if s = 0 then 4 else 0) 4 =
      {1, 2, 3} := by
  native_decide

example :
    DelayedFeedback.outstandingAt (fun s => if s = 0 then 4 else 0) 4 =
      {0} := by
  native_decide

example :
    DelayedFeedback.maxOutstandingBeforeThrough
      (fun s => if s = 0 then 4 else 0) 4 = 1 := by
  native_decide

example :
    DelayedFeedback.paperMissingAtEnd
      (fun s => if s = 1 then 2 else 0) 1 = {0} := by
  native_decide

example :
    DelayedFeedback.paperMissingCount
      (fun s => if s = 1 then 2 else 0) 1 = 1 := by
  native_decide

example :
    DelayedFeedback.paperSigmaMaxThrough
      (fun s => if s = 1 then 2 else 0) 2 = 1 := by
  native_decide

example :
    (DelayedFeedback.actionTimeViewAt
      (fun s => if s = 0 then 4 else 0)
      (fun s => s)
      (fun s => s + 10)
      4).observedLoss 0 = none := by
  native_decide

example :
    (DelayedFeedback.actionTimeViewAt
      (fun s => if s = 0 then 4 else 0)
      (fun s => s)
      (fun s => s + 10)
      4).observedLoss 1 = some 11 := by
  native_decide

example :
    DelayedFeedback.newlyObservedBefore
      (fun s => if s = 0 then 4 else 0) {1, 2} 4 = {3} := by
  native_decide

example :
    DelayedFeedback.processAllNew
      (fun s => if s = 0 then 4 else 0) {1, 2} 4 = {1, 2, 3} := by
  native_decide

example :
    let active : Finset (Fin 3) := {0, 1}
    let inactiveProbability : Fin 3 → ℝ := fun i => if i = 2 then 1 / 4 else 0
    Finset.univ.sum
      (DelayedFeedback.delayedSAPOProbability active inactiveProbability) =
        1 := by
  apply DelayedFeedback.sum_delayedSAPOProbability_eq_one
  simp
