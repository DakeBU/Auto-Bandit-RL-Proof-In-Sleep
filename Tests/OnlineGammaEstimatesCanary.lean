import BanditRLProof.OnlineGammaEstimates

open scoped Topology
open Filter Finset Set BanditRL.OnlineGamma
namespace BanditRL.OnlineGamma.Canary
noncomputable section

theorem sum_reciprocalDifference_neg_one_two :
  (∑ k ∈ range 2, reciprocalDifference (-1) k) = -2 := by
  exact (sum_reciprocalDifference (-1) 2).trans (by norm_num)

theorem logGammaSeq_derivatives_zero_at_two :
  HasDerivAt (fun y : ℝ => Real.BohrMollerup.logGammaSeq y 0) (-(1/2 : ℝ)) 2 ∧
  HasDerivAt (logGammaSlopeApprox 0) (1/4 : ℝ) 2 := by
  have h := hasDerivAt_logGammaSeq_and_slopeApprox 0 2 (by norm_num)
  have h₁ : logGammaSlopeApprox 0 2 = -(1/2 : ℝ) := by
    norm_num [logGammaSlopeApprox, Finset.sum_range_succ]
  have h₂ : logGammaCurvatureApprox 0 2 = (1/4 : ℝ) := by
    norm_num [logGammaCurvatureApprox, Finset.sum_range_succ]
  rw [h₁, h₂] at h
  exact h

theorem logGammaSeq_derivatives_one_at_one :
  HasDerivAt (fun y : ℝ => Real.BohrMollerup.logGammaSeq y 1) (-(3/2 : ℝ)) 1 ∧
  HasDerivAt (logGammaSlopeApprox 1) (5/4 : ℝ) 1 := by
  have h := hasDerivAt_logGammaSeq_and_slopeApprox 1 1 (by norm_num)
  have h₁ : logGammaSlopeApprox 1 1 = -(3/2 : ℝ) := by
    norm_num [logGammaSlopeApprox, Finset.sum_range_succ]
  have h₂ : logGammaCurvatureApprox 1 1 = (5/4 : ℝ) := by
    norm_num [logGammaCurvatureApprox, Finset.sum_range_succ]
  rw [h₁, h₂] at h
  exact h

theorem uniform_tails_endpoint_limits_and_prefixes :
  Tendsto (fun N : ℕ => ∑ k ∈ range N, compensatedReciprocal k 1) atTop
    (𝓝 (∑' k : ℕ, compensatedReciprocal k 1)) ∧
  Tendsto (fun N : ℕ => ∑ k ∈ range N, shiftedInvSq k 2) atTop
    (𝓝 (∑' k : ℕ, shiftedInvSq k 2)) ∧
  (∑ k ∈ range 0, compensatedReciprocal k 1) = 0 ∧ (∑ k ∈ range 0, shiftedInvSq k 2) = 0 ∧
  (∑ k ∈ range 1, compensatedReciprocal k 1) = 1/2 ∧ (∑ k ∈ range 1, shiftedInvSq k 2) = 1/9 := by
  obtain ⟨hd, hs⟩ := tendstoUniformlyOn_compensatedReciprocal_and_shiftedInvSq 1 2
    (by norm_num) (by norm_num)
  have hleft : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := by constructor <;> norm_num
  have hright : (2 : ℝ) ∈ Icc (1 : ℝ) 2 := by constructor <;> norm_num
  refine ⟨hd.tendsto_at hleft, hs.tendsto_at hright, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · norm_num [compensatedReciprocal, Finset.sum_range_succ]
  · norm_num [shiftedInvSq, Finset.sum_range_succ]

end
end BanditRL.OnlineGamma.Canary
