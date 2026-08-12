import BanditRLProof.Algorithms.KLUCBGeneratedRegret

open BanditRLProof MeasureTheory

#check BanditRLProof.KLUCB.bernoulliKL
#check BanditRLProof.KLUCB.half_sq_sub_le_bernoulliKLCore
#check BanditRLProof.KLUCB.bernoulliKLCore_le_sq_div
#check BanditRLProof.KLUCB.index_zero_count
#check BanditRLProof.KLUCB.historyPolicy
#check BanditRLProof.KLUCB.pairHistory_eq_finitePairHistoryOfTrace
#check BanditRLProof.KLUCB.generatedIndexAt_le_selected_of_K_le
#check BanditRLProof.KLUCB.measure_generatedKLAllTimeBadEvent_le_trajMeasure
#check BanditRLProof.KLUCB.allHorizonPullCount_of_not_badEvent
#check BanditRLProof.KLUCB.lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le_trajMeasure

#print axioms BanditRLProof.KLUCB.bernoulliKL_self
#print axioms BanditRLProof.KLUCB.half_sq_sub_le_bernoulliKLCore
#print axioms BanditRLProof.KLUCB.generatedIndexAt_le_selected_of_K_le
#print axioms BanditRLProof.KLUCB.measure_generatedKLAllTimeBadEvent_le_trajMeasure
#print axioms BanditRLProof.KLUCB.lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le_trajMeasure

example (p budget : Real)
    (hp : BanditRLProof.KLUCB.IsBernoulliParameter p)
    (hbudget : 0 <= budget) :
    BanditRLProof.KLUCB.index p 0 budget = 1 := by
  exact BanditRLProof.KLUCB.index_zero_count hp hbudget
