import BanditRLProof.OnlineSubgradientBasic
import BanditRLProof.OnlineSubgradientAbsolute
import BanditRLProof.OnlineHinge
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
open Set
namespace BanditRL.OnlineConvex
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem theorem_2_28 [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : F → EReal) (hp : SourceProper f) (A : E →L[ℝ] F) (b : F) (x : E) :
    A.adjoint '' (SourceSubdifferential f (A x + b)) ⊆
      SourceSubdifferential (fun y => f (A y + b)) x := by
  intro q hq
  rcases hq with ⟨g, hg, rfl⟩
  intro y
  have hi := hg (A y + b)
  have hm : (A y + b) - (A x + b) = A (y - x) := by
    rw [A.map_sub]
    abel
  rw [hm, ← ContinuousLinearMap.adjoint_inner_left A (y - x) g] at hi
  exact hi

end BanditRL.OnlineConvex

namespace AffineProbe
open Set BanditRL.OnlineConvex
noncomputable def doubleMap : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

theorem double_adjoint (g : ℝ) : doubleMap.adjoint g = 2 * g := by
  have h := ContinuousLinearMap.adjoint_inner_left doubleMap (1 : ℝ) g
  change (1 : ℝ) * (doubleMap.adjoint g) = (2 * 1) * g at h
  nlinarith

theorem absolute_proper : SourceProper (fun y : ℝ => ((|y| : ℝ) : EReal)) := by
  exact ⟨fun y => EReal.coe_ne_bot _, 0, 0, by norm_num⟩

theorem nonzero_shifted_support :
    (1 : ℝ) ∈ SourceSubdifferential
      (fun y : ℝ => ((|doubleMap y + 1| : ℝ) : EReal)) (-1/2) := by
  have hp : doubleMap (-1/2) + 1 = 0 := by
    change (2 : ℝ) * (-1/2) + 1 = 0
    norm_num
  have hg : (1/2 : ℝ) ∈ SourceSubdifferential
      (fun y : ℝ => ((|y| : ℝ) : EReal)) (doubleMap (-1/2) + 1) := by
    rw [hp, abs_subgradient_zero]
    norm_num
  have hi := theorem_2_28 (fun y : ℝ => ((|y| : ℝ) : EReal)) absolute_proper
    doubleMap 1 (-1/2)
  have hout := hi (mem_image_of_mem doubleMap.adjoint hg)
  rw [double_adjoint] at hout
  norm_num at hout
  exact hout

def negAbsLoss (y : ℝ) : EReal := ((-|y| : ℝ) : EReal)

theorem neg_abs_proper : SourceProper negAbsLoss := by
  exact ⟨fun y => EReal.coe_ne_bot _, 0, 0, by simp [negAbsLoss]⟩

theorem neg_abs_support_empty : SourceSubdifferential negAbsLoss 0 = ∅ := by
  ext g
  constructor
  · intro hg
    have h1 := hg 1
    have hm := hg (-1)
    rw [← EReal.coe_add] at h1 hm
    have h1r := EReal.coe_le_coe_iff.mp h1
    have hmr := EReal.coe_le_coe_iff.mp hm
    change -|(0 : ℝ)| + (1 - 0) * g ≤ -|(1 : ℝ)| at h1r
    change -|(0 : ℝ)| + (-1 - 0) * g ≤ -|(-1 : ℝ)| at hmr
    norm_num at h1r hmr
    linarith
  · intro hg
    exact False.elim hg

theorem proper_nonconvex_strict_inclusion :
    (0 : ℝ →L[ℝ] ℝ).adjoint '' SourceSubdifferential negAbsLoss 0 ⊆
      SourceSubdifferential (fun y : ℝ => negAbsLoss ((0 : ℝ →L[ℝ] ℝ) y + 0)) 3 ∧
    (0 : ℝ →L[ℝ] ℝ).adjoint '' SourceSubdifferential negAbsLoss 0 = ∅ ∧
    SourceSubdifferential (fun y : ℝ => negAbsLoss ((0 : ℝ →L[ℝ] ℝ) y + 0)) 3 = {0} ∧
    (0 : ℝ →L[ℝ] ℝ).adjoint '' SourceSubdifferential negAbsLoss 0 ≠
      SourceSubdifferential (fun y : ℝ => negAbsLoss ((0 : ℝ →L[ℝ] ℝ) y + 0)) 3 := by
  have hl : (0 : ℝ →L[ℝ] ℝ).adjoint '' SourceSubdifferential negAbsLoss 0 = ∅ := by
    rw [neg_abs_support_empty]
    simp
  have hr : SourceSubdifferential
      (fun y : ℝ => negAbsLoss ((0 : ℝ →L[ℝ] ℝ) y + 0)) 3 = {0} := by
    have he : (fun y : ℝ => negAbsLoss ((0 : ℝ →L[ℝ] ℝ) y + 0)) =
        (fun y : ℝ => ((inner ℝ (0 : ℝ) y + 0 : ℝ) : EReal)) := by
      funext y
      simp [negAbsLoss]
    rw [he, affine_subdifferential]
  refine ⟨?_, hl, hr, ?_⟩
  · simpa using theorem_2_28 negAbsLoss neg_abs_proper (0 : ℝ →L[ℝ] ℝ) 0 3
  · rw [hl, hr]
    simp

#print axioms AffineProbe.double_adjoint
#print axioms AffineProbe.nonzero_shifted_support
#print axioms AffineProbe.neg_abs_support_empty
#print axioms AffineProbe.proper_nonconvex_strict_inclusion
end AffineProbe
