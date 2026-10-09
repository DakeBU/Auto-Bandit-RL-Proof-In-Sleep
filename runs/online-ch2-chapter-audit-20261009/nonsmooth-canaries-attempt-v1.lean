/-
Five public concrete tests of the frozen nonsmooth terminals. C004 compares
ambient and tangential differentiability at the same plane point (1,3).
Zero-normal and dimension-zero cases are explicit boundary tests, not
substitutes for the nondegenerate shifted/positive/negative/plane cases.
These canaries do not establish chapter or whole-book acceptance.
-/
import BanditRLProof.OnlineNonsmoothExamples
import Tests.OnlineGradientDescentSourceCanary

noncomputable section
open scoped InnerProductSpace
open Tests.OnlineGradientDescentSource
namespace Tests.OnlineNonsmoothExamples

theorem source_shift_ten :
    ConvexOn ℝ Set.univ (fun w : ℝ => |w - 10|) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 10 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 9 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 11 := by
  have h := BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff (10 : ℝ)
  refine ⟨h.1, ?_, (h.2 9).mpr (by norm_num), (h.2 11).mpr (by norm_num)⟩
  intro hd
  exact ((h.2 10).mp hd) rfl

theorem positive_negative_labels :
    ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) (1 / 6) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) (-1 / 6) ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) 0 ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) 0 ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) := by
  have hp := BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff (2 : ℝ) (3 : ℝ)
  have hn := BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff (-2 : ℝ) (3 : ℝ)
  refine ⟨hp.1, hn.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hd
    have h := (hp.2.1 (1 / 6)).mp hd
    norm_num [RCLike.inner_apply] at h
  · intro hd
    have h := (hn.2.1 (-1 / 6)).mp hd
    norm_num [RCLike.inner_apply] at h
  · exact (hp.2.1 0).mpr (by norm_num)
  · exact (hn.2.1 0).mpr (by norm_num)
  · intro hd
    have h := hp.2.2.mp hd
    norm_num at h
  · intro hd
    have h := hn.2.2.mp hd
    norm_num at h

theorem zero_label_and_feature (y z : ℝ) :
    Differentiable ℝ (fun w : ℝ => max (1 - 0 * inner ℝ z w) 0) ∧
      Differentiable ℝ (fun w : ℝ => max (1 - y * inner ℝ (0 : ℝ) w) 0) ∧
      ∀ w : ℝ, max (1 - 0 * inner ℝ z w) 0 = 1 ∧
        max (1 - y * inner ℝ (0 : ℝ) w) 0 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff (0 : ℝ) z).2.2.mpr
      (by simp)
  · exact (BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff y (0 : ℝ)).2.2.mpr
      (by simp)
  · intro w
    simp

theorem plane_ambient_and_tangential :
    ¬ DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0)
        (e0 + (3 : ℝ) • e1) ∧
      DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0) e1 ∧
      DifferentiableAt ℝ (fun t : ℝ => max (1 - inner ℝ e0 (e0 + (3 + t) • e1)) 0) 0 := by
  have h := BanditRL.OnlineConvex.hinge_convex_differentiable_iff e0
  refine ⟨?_, (h.2 e1).mpr (by simp), ?_⟩
  · intro hd
    have hm := (h.2 (e0 + (3 : ℝ) • e1)).mp hd
    simp [inner_add_right, real_inner_smul_right] at hm
  · have hc : (fun t : ℝ => max (1 - inner ℝ e0 (e0 + (3 + t) • e1)) 0) =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext t
      simp [inner_add_right, real_inner_smul_right]
    rw [hc]
    exact differentiableAt_const 0

theorem dimension_zero (y : ℝ) (z : EuclideanSpace ℝ (Fin 0)) :
    Differentiable ℝ
        (fun w : EuclideanSpace ℝ (Fin 0) => max (1 - y * inner ℝ z w) 0) ∧
      ∀ w : EuclideanSpace ℝ (Fin 0), max (1 - y * inner ℝ z w) 0 = 1 := by
  refine ⟨?_, ?_⟩
  · exact (BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff y z).2.2.mpr
      (Subsingleton.elim _ _)
  · intro w
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz]

end Tests.OnlineNonsmoothExamples
