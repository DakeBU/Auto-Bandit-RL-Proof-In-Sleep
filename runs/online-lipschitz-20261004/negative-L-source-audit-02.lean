import BanditRLProof.OnlineHinge
import Mathlib.Analysis.InnerProductSpace.PiL2
noncomputable section
open Set BanditRL.OnlineConvex
namespace LipschitzSourceAudit
abbrev Z := EuclideanSpace ℝ (Fin 0)
def zeroLoss (_ : Z) : EReal := (0 : ℝ)
theorem negative_constant_zero_dimension :
    SourceProper zeroLoss ∧ IsConvexExtended zeroLoss ∧
    (∀ x y : Z, |(zeroLoss x).toReal - (zeroLoss y).toReal| ≤ (-1 : ℝ) * ‖x-y‖) ∧
    ¬ (∀ x : Z, ∀ g ∈ SourceSubdifferential zeroLoss x, ‖g‖ ≤ (-1 : ℝ)) := by
  have hp : SourceProper zeroLoss :=
    ⟨fun _ => EReal.coe_ne_bot _, 0, 0, rfl⟩
  have hc : IsConvexExtended zeroLoss := by
    simpa [zeroLoss] using affine_convex (0 : Z) 0
  refine ⟨hp, hc, ?_, ?_⟩
  · intro x y
    have hxy : x = y := Subsingleton.elim x y
    simp [hxy, zeroLoss]
  · intro h
    have hg : (0 : Z) ∈ SourceSubdifferential zeroLoss (0 : Z) := by
      intro y
      simp [zeroLoss]
    have h0 := h 0 0 hg
    norm_num at h0
#print axioms LipschitzSourceAudit.negative_constant_zero_dimension
end LipschitzSourceAudit
