import BanditRLProof.OnlineSubgradientAbsolute

namespace AbsoluteZeroProbe
open BanditRL.OnlineConvex Set

theorem zero_boundary_canary :
    (-1 : ℝ) ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 0 ∧
    (1 : ℝ) ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 0 ∧
    (1 / 2 : ℝ) ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 0 ∧
    (2 : ℝ) ∉ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 0 := by
  norm_num [abs_subgradient_zero]

theorem zero_is_not_a_singleton :
    ¬ ∃ g : ℝ, SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 0 = {g} := by
  rintro ⟨g, hg⟩
  have hm : (-1 : ℝ) ∈ ({g} : Set ℝ) := by
    rw [← hg, abs_subgradient_zero]
    norm_num
  have hp : (1 : ℝ) ∈ ({g} : Set ℝ) := by
    rw [← hg, abs_subgradient_zero]
    norm_num
  have hm' : (-1 : ℝ) = g := hm
  have hp' : (1 : ℝ) = g := hp
  linarith

#print axioms zero_boundary_canary
#print axioms zero_is_not_a_singleton
end AbsoluteZeroProbe

namespace AbsoluteAllPointsProbe
open BanditRL.OnlineConvex Set

theorem source_three_branches_canary :
    SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 2 = {(1 : ℝ)} ∧
    SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) (-2) = {(-1 : ℝ)} ∧
    SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 0 = Icc (-1 : ℝ) 1 := by
  constructor
  · have h := example_2_24 2
    norm_num at h
    exact h
  constructor
  · have h := example_2_24 (-2)
    norm_num at h
    exact h
  · have h := example_2_24 0
    norm_num at h
    exact h

#print axioms source_three_branches_canary
end AbsoluteAllPointsProbe
