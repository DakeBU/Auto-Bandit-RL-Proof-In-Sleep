import BanditRLProof.OnlineLearningAsymptotic
import BanditRLProof.OnlineLearningInformation
open BanditRL.OnlineLearning
example : NoRegret (Set.Icc (0:ℝ) 1)
    (fun t x => (x - (if t = 0 then 0 else 1))^2)
    (meanPredict (fun t => if t = 0 then 0 else 1)) := by
  apply meanPredict_noRegret
  intro t
  split_ifs <;> norm_num
#print axioms BanditRL.OnlineLearning.meanPredict_noRegret
#print axioms BanditRL.OnlineLearning.meanPredict_independent
