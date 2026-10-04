import BanditRLProof.OnlineHinge
import BanditRLProof.OnlineNormalCone
import BanditRLProof.OnlineSubgradientAbsolute
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import BanditRLProof.OnlineSubgradientDifferentiability
noncomputable section
open Set
open scoped Topology NNReal
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite values on V and the actual all-pairs Lipschitz inequality.
The constant is explicitly nonnegative, including zero. -/
def SourceLipschitzOn (f : E → EReal) (V : Set E) (L : ℝ≥0) : Prop :=
  (∀ x ∈ V, ∃ a : ℝ, f x = (a : EReal)) ∧
    ∀ x ∈ V, ∀ y ∈ V, |(f x).toReal - (f y).toReal| ≤ (L : ℝ) * ‖x - y‖

theorem theorem_2_30 [FiniteDimensional ℝ E]
    (f : E → EReal) (hp : SourceProper f) (hc : IsConvexExtended f) (L : ℝ≥0) :
    SourceLipschitzOn f (interior (effectiveDomain f)) L ↔
      ∀ x ∈ interior (effectiveDomain f), ∀ g ∈ SourceSubdifferential f x,
        ‖g‖ ≤ (L : ℝ) := by
  constructor
  · intro hl x hx g hg
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
    apply subgradient_norm_le_lipschitz_ball f x r hr L ?_ ?_ g hg
    · intro y hy
      exact hl.1 y (hball hy)
    · apply LipschitzOnWith.of_dist_le_mul
      intro y hy z hz
      simpa only [Real.dist_eq, dist_eq_norm] using hl.2 y (hball hy) z (hball hz)
  · intro hb
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxdom : x ∈ effectiveDomain f := interior_subset hx
      exact ⟨(f x).toReal,
        (EReal.coe_toReal (ne_of_lt hxdom) (hp.1 x)).symm⟩
    · intro x hx y hy
      obtain ⟨gx, hgx⟩ := subgradient_exists_of_domain_interior f hp hc x hx
      obtain ⟨gy, hgy⟩ := subgradient_exists_of_domain_interior f hp hc y hy
      have hxdom : x ∈ effectiveDomain f := interior_subset hx
      have hydom : y ∈ effectiveDomain f := interior_subset hy
      have hxv := EReal.coe_toReal (ne_of_lt hxdom) (hp.1 x)
      have hyv := EReal.coe_toReal (ne_of_lt hydom) (hp.1 y)
      have hxy := hgx y
      have hyx := hgy x
      rw [← hxv, ← hyv, ← EReal.coe_add] at hxy
      rw [← hyv, ← hxv, ← EReal.coe_add] at hyx
      have hxyR := EReal.coe_le_coe_iff.mp hxy
      have hyxR := EReal.coe_le_coe_iff.mp hyx
      have hxg : -(inner ℝ gx (y - x)) ≤ (L : ℝ) * ‖x - y‖ := calc
        -(inner ℝ gx (y - x)) ≤ |inner ℝ gx (y - x)| := neg_le_abs _
        _ ≤ ‖gx‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
        _ ≤ (L : ℝ) * ‖y - x‖ := mul_le_mul_of_nonneg_right (hb x hx gx hgx) (norm_nonneg _)
        _ = (L : ℝ) * ‖x - y‖ := by rw [norm_sub_rev]
      have hyg : -(inner ℝ gy (x - y)) ≤ (L : ℝ) * ‖x - y‖ := calc
        -(inner ℝ gy (x - y)) ≤ |inner ℝ gy (x - y)| := neg_le_abs _
        _ ≤ ‖gy‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
        _ ≤ (L : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_right (hb y hy gy hgy) (norm_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith

end BanditRL.OnlineConvex

namespace LipschitzProbe
open Set BanditRL.OnlineConvex
open scoped NNReal

def absLoss (x : ℝ) : EReal := ((|x| : ℝ) : EReal)
theorem abs_proper : SourceProper absLoss :=
  ⟨fun _ => EReal.coe_ne_bot _, 0, 0, by simp [absLoss]⟩
theorem abs_domain : effectiveDomain absLoss = univ := by
  ext x
  simp [effectiveDomain, absLoss]
theorem abs_convex : IsConvexExtended absLoss := by
  rw [convexExtended_iff_toReal absLoss abs_proper.1, abs_domain]
  simpa [absLoss, Real.norm_eq_abs] using
    (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℝ)))
theorem abs_lipschitz : SourceLipschitzOn absLoss (interior (effectiveDomain absLoss)) 1 := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ⟨|x|, rfl⟩
  · intro x hx y hy
    simpa [absLoss, Real.norm_eq_abs] using abs_abs_sub_abs_le_abs_sub x y

theorem abs_all_supports_and_nonzero :
    (∀ x g : ℝ, g ∈ SourceSubdifferential absLoss x → ‖g‖ ≤ 1) ∧
    (1 : ℝ) ∈ SourceSubdifferential absLoss 2 ∧
    (-1 : ℝ) ∈ SourceSubdifferential absLoss (-2) := by
  have hb := (theorem_2_30 absLoss abs_proper abs_convex 1).mp abs_lipschitz
  refine ⟨?_, ?_, ?_⟩
  · intro x g hg
    exact hb x (by simp [abs_domain]) g hg
  · change (1 : ℝ) ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 2
    rw [abs_subgradient_positive 2 (by norm_num)]
    simp
  · change (-1 : ℝ) ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) (-2)
    rw [abs_subgradient_negative (-2) (by norm_num)]
    simp

def linearLoss (x : ℝ) : EReal := ((inner ℝ (3 : ℝ) x + 0 : ℝ) : EReal)
theorem linear_proper : SourceProper linearLoss := affine_proper (3 : ℝ) 0
theorem linear_convex : IsConvexExtended linearLoss := affine_convex (3 : ℝ) 0

theorem linear_three_reverse :
    SourceLipschitzOn linearLoss (interior (effectiveDomain linearLoss)) 3 := by
  apply (theorem_2_30 linearLoss linear_proper linear_convex 3).mpr
  intro x hx g hg
  have he : SourceSubdifferential linearLoss x = {(3 : ℝ)} := affine_subdifferential 3 0 x
  rw [he] at hg
  have hge : g = 3 := mem_singleton_iff.mp hg
  subst g
  norm_num

def zeroLoss (_ : ℝ) : EReal := (0 : ℝ)
theorem zero_proper : SourceProper zeroLoss := ⟨fun _ => EReal.coe_ne_bot _, 0, 0, rfl⟩
theorem zero_convex : IsConvexExtended zeroLoss := by
  simpa [zeroLoss] using affine_convex (0 : ℝ) 0

theorem zero_constant :
    SourceLipschitzOn zeroLoss (interior (effectiveDomain zeroLoss)) 0 ∧
    (∀ x ∈ interior (effectiveDomain zeroLoss), ∀ g ∈ SourceSubdifferential zeroLoss x, g = 0) := by
  have hl : SourceLipschitzOn zeroLoss (interior (effectiveDomain zeroLoss)) 0 := by
    refine ⟨fun x hx => ⟨0, rfl⟩, ?_⟩
    intro x hx y hy
    simp [zeroLoss]
  refine ⟨hl, ?_⟩
  have hb := (theorem_2_30 zeroLoss zero_proper zero_convex 0).mp hl
  intro x hx g hg
  exact norm_eq_zero.mp (le_antisymm (hb x hx g hg) (norm_nonneg _))

theorem singleton_empty_interior_and_boundary :
    interior (effectiveDomain (extendedIndicator ({0} : Set ℝ))) = ∅ ∧
    SourceLipschitzOn (extendedIndicator ({0} : Set ℝ))
      (interior (effectiveDomain (extendedIndicator ({0} : Set ℝ)))) 0 ∧
    (3 : ℝ) ∈ SourceSubdifferential (extendedIndicator ({0} : Set ℝ)) 0 ∧
    ¬ ‖(3 : ℝ)‖ ≤ 0 := by
  classical
  have hi : interior (effectiveDomain (extendedIndicator ({0} : Set ℝ))) = ∅ := by
    rw [effectiveDomain_indicator, interior_singleton]
  have hp : SourceProper (extendedIndicator ({0} : Set ℝ)) :=
    (sourceProper_indicator_iff _).mpr (singleton_nonempty 0)
  have hc : IsConvexExtended (extendedIndicator ({0} : Set ℝ)) :=
    (convex_indicator_iff _).mpr (convex_singleton 0)
  refine ⟨hi, ?_, ?_, by norm_num⟩
  · apply (theorem_2_30 _ hp hc 0).mpr
    intro x hx g hg
    rw [hi] at hx
    exact False.elim hx
  · intro y
    by_cases hy : y = 0
    · subst y
      simp [extendedIndicator]
    · simp [extendedIndicator, hy]

def halflineLoss : ℝ → EReal := extendedIndicator (Ici 0)
theorem halfline_proper : SourceProper halflineLoss :=
  (sourceProper_indicator_iff (Ici (0 : ℝ))).mpr ⟨0, by simp⟩
theorem halfline_convex : IsConvexExtended halflineLoss :=
  (convex_indicator_iff _).mpr (convex_Ici 0)
theorem halfline_lipschitz : SourceLipschitzOn halflineLoss (interior (effectiveDomain halflineLoss)) 0 := by
  classical
  have hi : interior (effectiveDomain halflineLoss) = Ioi 0 := by
    simp [halflineLoss, effectiveDomain_indicator, interior_Ici]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hi] at hx
    have hxpos : (0 : ℝ) < x := mem_Ioi.mp hx
    exact ⟨0, by simp [halflineLoss, extendedIndicator, hxpos.le]⟩
  · intro x hx y hy
    rw [hi] at hx hy
    have hxpos : (0 : ℝ) < x := mem_Ioi.mp hx
    have hypos : (0 : ℝ) < y := mem_Ioi.mp hy
    simp [halflineLoss, extendedIndicator, hxpos.le, hypos.le]

theorem halfline_interior_not_whole_domain :
    (∀ x ∈ interior (effectiveDomain halflineLoss), ∀ g ∈ SourceSubdifferential halflineLoss x, g = 0) ∧
    (-2 : ℝ) ∈ SourceSubdifferential halflineLoss 0 ∧
    ¬ ‖(-2 : ℝ)‖ ≤ 0 ∧
    (∀ x y : ℝ, |(halflineLoss x).toReal - (halflineLoss y).toReal| ≤ (0 : ℝ) * ‖x-y‖) ∧
    ¬ SourceLipschitzOn halflineLoss univ 0 := by
  classical
  refine ⟨?_, ?_, by norm_num, ?_, ?_⟩
  · have hb := (theorem_2_30 halflineLoss halfline_proper halfline_convex 0).mp halfline_lipschitz
    intro x hx g hg
    exact norm_eq_zero.mp (le_antisymm (hb x hx g hg) (norm_nonneg _))
  · intro y
    by_cases hy : 0 ≤ y
    · have hR : inner ℝ (-2 : ℝ) (y-0) ≤ 0 := by
        change (y-0) * (-2) ≤ 0
        nlinarith
      have hr : ((inner ℝ (-2 : ℝ) (y-0) : ℝ) : EReal) ≤ (0 : EReal) :=
        EReal.coe_le_coe_iff.mpr hR
      simpa [halflineLoss, extendedIndicator, hy] using hr
    · simp [halflineLoss, extendedIndicator, hy]
  · intro x y
    have hval (z : ℝ) : (halflineLoss z).toReal = 0 := by
      by_cases hz : 0 ≤ z <;> simp [halflineLoss, extendedIndicator, hz]
    simp [hval]
  · intro hl
    obtain ⟨a, ha⟩ := hl.1 (-1) (mem_univ _)
    norm_num [halflineLoss, extendedIndicator] at ha

abbrev Z := EuclideanSpace ℝ (Fin 0)
def nineLoss (_ : Z) : EReal := (9 : ℝ)
theorem zero_dimension : SourceLipschitzOn nineLoss (interior (effectiveDomain nineLoss)) 0 := by
  have hp : SourceProper nineLoss := ⟨fun _ => EReal.coe_ne_bot _, 0, 9, rfl⟩
  have hc : IsConvexExtended nineLoss := by
    simpa [nineLoss] using affine_convex (0 : Z) 9
  apply (theorem_2_30 nineLoss hp hc 0).mpr
  intro x hx g hg
  have hg0 : g = 0 := Subsingleton.elim _ _
  simp [hg0]

#print axioms LipschitzProbe.abs_all_supports_and_nonzero
#print axioms LipschitzProbe.linear_three_reverse
#print axioms LipschitzProbe.zero_constant
#print axioms LipschitzProbe.singleton_empty_interior_and_boundary
#print axioms LipschitzProbe.halfline_interior_not_whole_domain
#print axioms LipschitzProbe.zero_dimension
end LipschitzProbe
