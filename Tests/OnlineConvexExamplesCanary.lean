import BanditRLProof

noncomputable section
open Set BanditRL.OnlineConvex
namespace Tests.OnlineConvexExamples

def affine (x : ℝ) : EReal := ((2 * x - 1 : ℝ) : EReal)

theorem affine_convex : IsConvexExtended affine := by
  have h := example_2_5 (E := ℝ) 2 (-1)
  have he : (fun x : ℝ => ((inner ℝ (2 : ℝ) x + (-1) : ℝ) : EReal)) = affine := by
    funext x
    change ((x * 2 + (-1) : ℝ) : EReal) = ((2 * x - 1 : ℝ) : EReal)
    congr 1
    ring
  rw [he] at h
  exact h

theorem norm_convex : IsConvexExtended (fun x : ℝ => ((|x| : ℝ) : EReal)) := by
  simpa only [Real.norm_eq_abs] using (example_2_6 (E := ℝ))

theorem nondegenerate : affine 0 = ((-1 : ℝ) : EReal) ∧
    affine 2 = ((3 : ℝ) : EReal) ∧
    (2, 3) ∈ realEpigraph affine ∧ (2, 2) ∉ realEpigraph affine := by
  have h0 : affine 0 = ((-1 : ℝ) : EReal) := by norm_num [affine]
  have h2 : affine 2 = ((3 : ℝ) : EReal) := by norm_num [affine]
  refine ⟨h0, h2, ?_, ?_⟩
  · change affine 2 ≤ ((3 : ℝ) : EReal)
    rw [h2]
  · change ¬ affine 2 ≤ ((2 : ℝ) : EReal)
    rw [h2]
    norm_cast

theorem norm_midpoint :
    (0 : EReal) < ((|-2| : ℝ) : EReal) ∧
    ((|(1 / 2 : ℝ) * (-2) + (1 / 2 : ℝ) * 2| : ℝ) : EReal) = 0 := by
  norm_num

example : IsConvexExtended (fun x : ℝ => ((inner ℝ (0 : ℝ) x + 0 : ℝ) : EReal)) :=
  example_2_5 0 0

example : ConvexOn ℝ univ (fun x : ℝ => |x|) :=
  (convexExtended_coe_iff _).mp norm_convex

#print axioms BanditRL.OnlineConvex.convexExtended_coe_iff
#print axioms BanditRL.OnlineConvex.example_2_5
#print axioms BanditRL.OnlineConvex.example_2_6
#print axioms affine_convex
#print axioms nondegenerate
end Tests.OnlineConvexExamples
