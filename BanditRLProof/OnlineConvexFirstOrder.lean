import BanditRLProof.OnlineConvexExtended
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section
open Set Filter
open scoped Topology
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem finitePart_eventually (f : E → EReal) (hbot : ∀ z, f z ≠ ⊥)
    (x : E) (hx : x ∈ interior (effectiveDomain f)) :
    ∀ᶠ z in 𝓝 x, ((f z).toReal : EReal) = f z := by
  filter_upwards [isOpen_interior.mem_nhds hx] with z hz
  have hzdom : z ∈ effectiveDomain f := interior_subset hz
  exact EReal.coe_toReal (ne_of_lt hzdom) (hbot z)

theorem convex_gradient_lower_bound (V : Set E) (f : E → ℝ) (hf : ConvexOn ℝ V f)
    (x y : E) (hx : x ∈ V) (hy : y ∈ V) (hd : DifferentiableAt ℝ f x) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  have hg := hd.hasGradientAt
  have hline : HasDerivAt (AffineMap.lineMap x y : ℝ → E) (y - x) 0 := by
    simpa only [AffineMap.lineMap_apply_module', one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x
  have hfd : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f x))
      (AffineMap.lineMap x y (0 : ℝ)) := by simpa using hg.hasFDerivAt
  have hc := hf.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
  have hb := hc.le_slope_of_hasDerivAt (by simpa using hx) (by simpa using hy)
    (by norm_num : (0 : ℝ) < 1) (hfd.comp_hasDerivAt 0 hline)
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one, InnerProductSpace.toDual_apply_apply] at hb
  linarith

theorem theorem_2_7 (f : E → EReal) (hbot : ∀ z, f z ≠ ⊥)
    (hf : IsConvexExtended f) (x : E) (hx : x ∈ interior (effectiveDomain f))
    (hd : DifferentiableAt ℝ (fun z => (f z).toReal) x) (y : E) :
    f x + ((inner ℝ (gradient (fun z => (f z).toReal) x) (y - x) : ℝ) : EReal) ≤ f y := by
  have hxval := (finitePart_eventually f hbot x hx).self_of_nhds
  have hxdom : x ∈ effectiveDomain f := by
    change f x < ⊤
    rw [← hxval]
    exact EReal.coe_lt_top _
  by_cases hy : y ∈ effectiveDomain f
  · have hb := convex_gradient_lower_bound (effectiveDomain f) (fun z => (f z).toReal)
      ((convexExtended_iff_toReal f hbot).mp hf) x y hxdom hy hd
    rw [← hxval, ← EReal.coe_toReal (ne_of_lt hy) (hbot y), ← EReal.coe_add]
    exact EReal.coe_le_coe hb
  · have hyt : f y = ⊤ := eq_top_iff.mpr (not_lt.mp hy)
    rw [hyt]
    exact le_top

end BanditRL.OnlineConvex
