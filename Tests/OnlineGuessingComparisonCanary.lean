import BanditRLProof

namespace Tests.OnlineGuessingComparison
open BanditRL.OnlineGradientDescent Finset

lemma actual_zero_stream_gap :
    (3/4 : ℝ) ≤
      regret unitInterval (1/16) (fun _ x => (x-0)^2) 1 0 64 -
      (∑ t ∈ range 64,
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by
  have h := guessing_vs_mean_lower 4 (by omega)
  norm_num at h ⊢
  exact h

#print axioms actual_zero_stream_gap
end Tests.OnlineGuessingComparison
