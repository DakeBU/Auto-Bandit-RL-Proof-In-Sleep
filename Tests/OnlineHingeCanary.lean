import BanditRLProof.OnlineHinge

namespace HingeProbe
open Set BanditRL.OnlineConvex

theorem strict_zero : SourceSubdifferential (sourceHinge (1 : ℝ)) 2 = {0} := by
  have hi : inner ℝ (1 : ℝ) (2 : ℝ) = 2 := by
    change (2 : ℝ) * 1 = 2
    norm_num
  rw [example_2_27, hi]
  norm_num

theorem strict_slope : SourceSubdifferential (sourceHinge (1 : ℝ)) 0 = {(-1 : ℝ)} := by
  rw [example_2_27]
  norm_num [RCLike.inner_apply]

theorem boundary_interval :
    SourceSubdifferential (sourceHinge (1 : ℝ)) 1 = Icc (-1 : ℝ) 0 := by
  rw [example_2_27]
  norm_num [RCLike.inner_apply]
  ext g
  constructor
  · rintro ⟨α, hα, he⟩
    subst g
    exact ⟨by linarith [hα.2], by linarith [hα.1]⟩
  · intro hg
    refine ⟨-g, ⟨by linarith [hg.2], by linarith [hg.1]⟩, ?_⟩
    simp

theorem actual_mixture_and_rejection :
    (-1/2 : ℝ) ∈ SourceSubdifferential (sourceHinge (1 : ℝ)) 1 ∧
    (-1/2 : ℝ) ∉ SourceActiveSubgradientUnion (hingeFamily (1 : ℝ)) 1 ∧
    (1 : ℝ) ∉ SourceSubdifferential (sourceHinge (1 : ℝ)) 1 := by
  rw [boundary_interval, hinge_active_zero (1 : ℝ) 1 (by norm_num)]
  norm_num [RCLike.inner_apply]

theorem zero_vector (x : ℝ) : SourceSubdifferential (sourceHinge (0 : ℝ)) x = {0} := by
  rw [example_2_27]
  simp

end HingeProbe
