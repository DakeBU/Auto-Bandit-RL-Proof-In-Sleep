import BanditRLProof.OnlineGuessingLower
import BanditRLProof.OnlineLearningFTL

open Set Finset
namespace BanditRL.OnlineGradientDescent

theorem meanPredict_zero_cumulativeLoss (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ range T,
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) = 1/4 := by
  have hp (t : ℕ) :
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2 =
        if t = 0 then (1/4 : ℝ) else 0 := by
    by_cases ht : t = 0
    · simp [BanditRL.OnlineLearning.meanPredict, ht]
      norm_num
    · simp [BanditRL.OnlineLearning.meanPredict,
        BanditRL.OnlineLearning.empiricalMean, ht]
  simp_rw [hp]
  simpa [hT] using (Finset.sum_ite_eq' (range T) 0 (fun _ => (1/4 : ℝ)))

end BanditRL.OnlineGradientDescent
