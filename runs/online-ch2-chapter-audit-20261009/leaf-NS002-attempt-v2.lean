/-
Orabona arXiv:1912.13213v10, Section2.2 opening paragraph, printed16/PDF28.
The shifted absolute and labelled hinge illustrate convex losses with genuine
ambient kinks. The exact pointwise criteria below distinguish an exceptional
point from global differentiability. The unrestricted hinge sentence needs
an explicit qualification: zero effective normal gives the constant1 loss.
The pinned source is unchanged; this qualification was separately reviewed,
and is not an author-endorsed erratum. Center10 is generalized to every real c.
Finite-dimensional real inner-product instances include all source Euclidean
dimensions, including0. These examples do not close Chapter2 or the book.
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import BanditRLProof.OnlineConvexExamples
import BanditRLProof.OnlineHinge
import BanditRLProof.OnlineSubgradientDifferentiability

noncomputable section
open Set
open scoped InnerProductSpace
namespace BanditRL.OnlineConvex

theorem shifted_absolute_convex_differentiable_iff (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c := by
  constructor
  · simpa [Function.comp_def, Real.norm_eq_abs] using
      (convexOn_univ_norm (E := ℝ)).comp_affineMap
        (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ c)
  · intro x
    constructor
    · intro hd hxc
      subst x
      have ht : DifferentiableAt ℝ (fun t : ℝ => t + c) 0 :=
        differentiableAt_id.add_const c
      have hd' : DifferentiableAt ℝ (fun w : ℝ => |w - c|) ((fun t : ℝ => t + c) 0) := by
        simpa using hd
      apply not_differentiableAt_abs_zero
      simpa [Function.comp_def] using hd'.comp 0 ht
    · intro hxc
      exact (differentiableAt_id.sub_const c).abs (sub_ne_zero.mpr hxc)

theorem hinge_convex_differentiable_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - inner ℝ a x) 0) ∧
      ∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - inner ℝ a w) 0) x ↔
        inner ℝ a x ≠ 1 := by
  have haffine : ConvexOn ℝ univ (fun x : E => 1 - inner ℝ a x) := by
    simpa [inner_neg_left, sub_eq_add_neg, add_comm] using
      (convexExtended_coe_iff (fun x : E => inner ℝ (-a) x + 1)).mp
        (affine_convex (-a) 1)
  have hconvex : ConvexOn ℝ univ (fun x : E => max (1 - inner ℝ a x) 0) := by
    exact haffine.sup (convexOn_const (0 : ℝ) convex_univ)
  have hext : IsConvexExtended (sourceHinge a) :=
    (convexExtended_coe_iff _).mpr hconvex
  refine ⟨hconvex, ?_⟩
  intro x
  have hfinite : ∃ r : ℝ, sourceHinge a x = (r : EReal) :=
    ⟨max (1 - inner ℝ a x) 0, rfl⟩
  constructor
  · intro hd hmargin
    have hsrc : SourceDifferentiableAt (sourceHinge a) x :=
      ⟨(fun w => max (1 - inner ℝ a w) 0), Filter.Eventually.of_forall (fun _ => rfl), hd⟩
    obtain ⟨g, hsingle⟩ := (theorem_2_22 (sourceHinge a) hext x hfinite).mp hsrc
    have hmargin0 : 1 - inner ℝ a x = 0 := by linarith
    have hset : SourceSubdifferential (sourceHinge a) x =
        {v | ∃ α ∈ Icc (0 : ℝ) 1, v = -(α • a)} := by
      simpa [hmargin0] using example_2_27 a x
    have hzero : (0 : E) ∈ SourceSubdifferential (sourceHinge a) x := by
      rw [hset]
      exact ⟨0, by norm_num, by simp⟩
    have hneg : -a ∈ SourceSubdifferential (sourceHinge a) x := by
      rw [hset]
      exact ⟨1, by norm_num, by simp⟩
    have hzero_eq : (0 : E) = g := by simpa only [hsingle, mem_singleton_iff] using hzero
    have hneg_eq : -a = g := by simpa only [hsingle, mem_singleton_iff] using hneg
    have ha : a = 0 := neg_eq_zero.mp (hneg_eq.trans hzero_eq.symm)
    simp [ha] at hmargin
  · intro hmargin
    have hmargin0 : 1 - inner ℝ a x ≠ 0 := sub_ne_zero.mpr hmargin.symm
    have hsingle : ∃ g : E, SourceSubdifferential (sourceHinge a) x = {g} := by
      by_cases hnegative : 1 - inner ℝ a x < 0
      · exact ⟨0, by simpa [hnegative] using example_2_27 a x⟩
      · exact ⟨-a, by simpa [hnegative, hmargin0] using example_2_27 a x⟩
    have hsrc := (theorem_2_22 (sourceHinge a) hext x hfinite).mpr hsingle
    simpa only [sourceHinge, EReal.toReal_coe] using
      (sourceDifferentiableAt_regular (sourceHinge a) x hsrc).2.2

end BanditRL.OnlineConvex
