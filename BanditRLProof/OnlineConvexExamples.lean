/-
Source: Orabona v10, Examples 2.5 and 2.6, printed p.10 / PDF p.22.
Every affine inner-product function and every norm is convex under the shared
real-height extended-real epigraph definition. Example 2.6 remains mandatory
main text although its proof is left as an exercise. The finite coercion iff
is a library bridge, not another numbered source theorem. General real normed
and inner-product spaces include the source finite-dimensional instances.
No boundedness or nonzero slope/value assumption. Existing code is preserved.
-/
import BanditRLProof.OnlineConvexExtended
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem convexExtended_coe_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) : IsConvexExtended (fun x => (f x : EReal)) ↔ ConvexOn ℝ univ f := by
  have hbot : ∀ x, (f x : EReal) ≠ ⊥ := fun x => EReal.coe_ne_bot _
  rw [convexExtended_iff_toReal _ hbot]
  have hd : effectiveDomain (fun x => (f x : EReal)) = (univ : Set E) := by
    ext x
    simp [effectiveDomain]
  simpa only [hd, EReal.toReal_coe]

theorem example_2_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) (b : ℝ) : IsConvexExtended (fun x => ((inner ℝ z x + b : ℝ) : EReal)) := by
  apply (convexExtended_coe_iff _).mpr
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a c ha hc hac
  simp only [inner_add_right, inner_smul_right, smul_eq_mul]
  nlinarith [congrArg (fun q : ℝ => q * b) hac]

theorem example_2_6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsConvexExtended (fun x : E => ((‖x‖ : ℝ) : EReal)) := by
  exact (convexExtended_coe_iff _).mpr convexOn_univ_norm

end BanditRL.OnlineConvex
