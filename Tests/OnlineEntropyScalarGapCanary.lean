import BanditRLProof.OnlineEntropyScalarGap

noncomputable section
namespace BanditRL.OnlineEntropy

theorem scalarGap_unit_contact :
    HasDerivAt scalarGap 0 1 ∧ HasDerivAt (deriv scalarGap) 0 1 ∧
    scalarGap 1 = 0 ∧ ¬ (∀ u : ℝ, 0 < u → 0 < deriv (deriv scalarGap) u) := by
  obtain ⟨ha,hb,_,_⟩ := scalarGap_curvature 1 (by norm_num)
  have ha0 : HasDerivAt scalarGap 0 1 := by convert ha using 1 <;> norm_num
  have hb0 : HasDerivAt (deriv scalarGap) 0 1 := by convert hb using 1 <;> norm_num
  exact ⟨ha0,hb0,scalarGap_nonneg.1,fun h => (h 1 (by norm_num)).ne' hb0.deriv⟩

theorem scalarGap_two_curvature :
    HasDerivAt (deriv scalarGap) (17/108) 2 ∧
    deriv (deriv scalarGap) 2 = 17/108 ∧ 0 < deriv (deriv scalarGap) 2 := by
  have h := (scalarGap_curvature 2 (by norm_num)).2.1
  have hd : HasDerivAt (deriv scalarGap) (17/108) 2 := by convert h using 1 <;> norm_num
  exact ⟨hd, hd.deriv, by rw [hd.deriv]; norm_num⟩

theorem log_three_lower_bound : (1 : ℝ) ≤ Real.log 3 := by
  have h := (positive_pair_log_ratio (3 : ℝ) 1 (by norm_num) (by norm_num)).1
  norm_num at h
  linarith

end BanditRL.OnlineEntropy
