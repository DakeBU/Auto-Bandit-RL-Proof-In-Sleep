import BanditRLProof.DelayedFeedback.Accounting
import BanditRLProof.DelayedFeedback.ActiveAllocation
import BanditRLProof.DelayedFeedback.ActionLaw
import BanditRLProof.DelayedFeedback.CausalView
import BanditRLProof.DelayedFeedback.Elimination
import BanditRLProof.DelayedFeedback.StochasticGoodEvent
import BanditRLProof.DelayedFeedback.StochasticGoodEventAssembly
import BanditRLProof.DelayedFeedback.StochasticGapOrderingAudit
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
#check DelayedFeedback.DelayedSAPOEliminationSnapshot
#check DelayedFeedback.DelayedSAPOEliminationSnapshot.eliminated
#check DelayedFeedback.DelayedSAPOEliminationSnapshot.remainingActive
#check DelayedFeedback.DelayedSAPOEliminationSnapshot.OptimalArmSurvivalCertificate
#check DelayedFeedback.DelayedSAPOEliminationSnapshot.optimal_mem_remainingActive_of_certificate
#check DelayedFeedback.DelayedSAPOEliminationSnapshot.remainingActive_nonempty_of_certificate
#check DelayedFeedback.DelayedSAPOEliminationSnapshot.sum_delayedSAPOProbability_after_elimination_eq_one
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.sourceUcbStar
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.EliminationGoodEvent
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.optimalMean_le_ucbStar_of_eliminationGoodEvent
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.optimalArmSurvivalCertificate_of_eliminationGoodEvent
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.optimal_mem_remainingActive_of_eliminationGoodEvent
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.eliminationGoodEventSet
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.optimalSurvivalEventSet
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.eliminationGoodEventSet_subset_optimalSurvivalEventSet
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.measure_optimalSurvivalEventSet_compl_le
#check DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.measure_optimalSurvivalEventSet_compl_le_of_goodEvent
#check DelayedFeedback.DelayedSAPOGoodEventComponent
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.componentFailure
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.failureSet
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.sourceGoodEventSet
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.sourceGoodEventSet_compl
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.measure_sourceGoodEventSet_compl_le_sum
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.quadraticFailureBudget
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.linearFailureBudget
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.quadraticFailureBudget_le_linearFailureBudget
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.measure_sourceGoodEventSet_compl_le_nine_div
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.measure_eliminationGoodEventSet_compl_le_nine_div
#check DelayedFeedback.DelayedSAPOGoodEventFailureFamily.measure_optimalSurvivalEventSet_compl_le_nine_div
#check DelayedFeedback.sourceEmpiricalWidthScale
#check DelayedFeedback.sourceEmpiricalWidthScale_antitone
#check DelayedFeedback.one_le_ten_mul_sourceEmpiricalWidthScale_of_count_le_96_mul_scale
#check DelayedFeedback.one_le_ten_mul_sourceEmpiricalWidthScale_two_log_of_small_count
#check DelayedFeedback.sourceEmpiricalWidthScale_one_one
#check DelayedFeedback.sourceEmpiricalWidthScale_one_four
#check DelayedFeedback.not_sourceEmpiricalWidthScale_one_le_four
#check DelayedFeedback.not_sourceEmpiricalWidthScale_horizon_four_one_le_four
#check DelayedFeedback.eight_mul_empiricalWidth_lt_gap_of_mem_eliminated
#check DelayedFeedback.gap_le_sixteen_mul_empiricalWidth_of_mem_remainingActive
#check DelayedFeedback.gap_le_sixteen_mul_empiricalWidth_of_mem_remainingActive_of_large_or_small_count
#check DelayedFeedback.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot
#check DelayedFeedback.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_large_or_small_count
#check DelayedFeedback.DelayedSAPOD10D12GapOrderingContract
#check DelayedFeedback.DelayedSAPOD10D12GapOrderingContract.surrogateGap
#check DelayedFeedback.DelayedSAPOD10D12GapOrderingContract.surrogateGap_le_gap
#check DelayedFeedback.DelayedSAPOD10D12GapOrderingContract.gap_le_two_mul_surrogateGap
#check DelayedFeedback.DelayedSAPOD10D12GapOrderingContract.d12_gap_ordering_chain
#check DelayedFeedback.DelayedSAPOD10D12GapOrderingContract.gap_le_twenty_mul_gap_of_eliminationPrefixIndex_le
#check DelayedFeedback.DelayedSAPOAllocation
#check DelayedFeedback.DelayedSAPOAllocation.probability
#check DelayedFeedback.DelayedSAPOAllocation.finiteActionDistribution
#check DelayedFeedback.DelayedSAPOAllocation.actionMeasure
#check DelayedFeedback.DelayedSAPOAllocation.actionMeasure_isProbabilityMeasure
#check DelayedFeedback.causalDelayedSAPOActionMeasureRule
#check DelayedFeedback.causalDelayedSAPOActionMeasureRule_isProbabilityMeasure
#check DelayedFeedback.causalDelayedSAPOActionMeasureRule_eq_of_observation_equivalent

#print axioms DelayedFeedback.DelayedSAPOEliminationSnapshot.optimal_mem_remainingActive_of_certificate
#print axioms DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.optimal_mem_remainingActive_of_eliminationGoodEvent
#print axioms DelayedFeedback.DelayedSAPOSourceConfidenceSnapshot.measure_optimalSurvivalEventSet_compl_le_of_goodEvent
#print axioms DelayedFeedback.DelayedSAPOGoodEventFailureFamily.measure_sourceGoodEventSet_compl_le_nine_div
#print axioms DelayedFeedback.DelayedSAPOGoodEventFailureFamily.measure_optimalSurvivalEventSet_compl_le_nine_div
#print axioms DelayedFeedback.sourceEmpiricalWidthScale_antitone
#print axioms DelayedFeedback.one_le_ten_mul_sourceEmpiricalWidthScale_of_count_le_96_mul_scale
#print axioms DelayedFeedback.one_le_ten_mul_sourceEmpiricalWidthScale_two_log_of_small_count
#print axioms DelayedFeedback.not_sourceEmpiricalWidthScale_one_le_four
#print axioms DelayedFeedback.not_sourceEmpiricalWidthScale_horizon_four_one_le_four
#print axioms DelayedFeedback.eight_mul_empiricalWidth_lt_gap_of_mem_eliminated
#print axioms DelayedFeedback.gap_le_sixteen_mul_empiricalWidth_of_mem_remainingActive
#print axioms DelayedFeedback.gap_le_sixteen_mul_empiricalWidth_of_mem_remainingActive_of_large_or_small_count
#print axioms DelayedFeedback.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot
#print axioms DelayedFeedback.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_large_or_small_count
#print axioms DelayedFeedback.DelayedSAPOD10D12GapOrderingContract.gap_le_twenty_mul_gap_of_eliminationPrefixIndex_le
#print axioms DelayedFeedback.DelayedSAPOAllocation.actionMeasure_isProbabilityMeasure
#print axioms DelayedFeedback.causalDelayedSAPOActionMeasureRule_eq_of_observation_equivalent

example : DelayedFeedback.sourceEmpiricalWidthScale 1 0 = 1 := by
  norm_num [DelayedFeedback.sourceEmpiricalWidthScale]

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

example :
    let snapshot :
        DelayedFeedback.DelayedSAPOEliminationSnapshot 3 := {
      active := {0, 1, 2}
      empiricalMean := fun i => if i = 0 then 1 / 4 else 3 / 4
      empiricalWidth := fun _ => 1 / 20
      ucbStar := 3 / 10
    }
    (0 : Fin 3) ∈ snapshot.remainingActive := by
  let snapshot : DelayedFeedback.DelayedSAPOEliminationSnapshot 3 := {
    active := {0, 1, 2}
    empiricalMean := fun i => if i = 0 then 1 / 4 else 3 / 4
    empiricalWidth := fun _ => 1 / 20
    ucbStar := 3 / 10
  }
  let mean : Fin 3 → ℝ := fun i => if i = 0 then 1 / 5 else 4 / 5
  apply DelayedFeedback.DelayedSAPOEliminationSnapshot.optimal_mem_remainingActive_of_certificate
    snapshot mean 0
  constructor
  · simp [snapshot]
  · norm_num [snapshot]
  · norm_num [snapshot, mean]
  · norm_num [snapshot, mean]
