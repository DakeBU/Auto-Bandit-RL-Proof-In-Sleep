import BanditRLProof

namespace Tests.OnlineFTLFailure
open BanditRL.OnlineLearning
lemma six_rounds :
    (∑ t ∈ Finset.range 6, failureCoefficient t * linearFTLPredict failureCoefficient (1/3) t) = 29/6 := by
  have h := (example_2_10 (1/3) (by norm_num) 6 (by omega)).1
  norm_num at h ⊢
  exact h
lemma actual_predictions : linearFTLPredict failureCoefficient (1/3) 0 = 1/3 ∧
    linearFTLPredict failureCoefficient (1/3) 1 = 1 ∧
    linearFTLPredict failureCoefficient (1/3) 2 = -1 := by
  norm_num [linearFTLPredict, prefixCoefficient, failureCoefficient]
end Tests.OnlineFTLFailure

#print axioms BanditRL.OnlineLearning.prefixCoefficient_eq_sum
#print axioms BanditRL.OnlineLearning.linearFTLPredict_prefix
#print axioms BanditRL.OnlineLearning.linearFTLPredict_mem
#print axioms BanditRL.OnlineLearning.linearFTLPredict_minimizes
#print axioms BanditRL.OnlineLearning.failure_prefixCoefficient
#print axioms BanditRL.OnlineLearning.failure_prediction
#print axioms BanditRL.OnlineLearning.example_2_10
#print axioms Tests.OnlineFTLFailure.six_rounds
#print axioms Tests.OnlineFTLFailure.actual_predictions
