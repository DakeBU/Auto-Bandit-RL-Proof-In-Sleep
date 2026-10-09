import BanditRLProof.OnlineBregmanExtended
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Data.Option.Basic

noncomputable section
open Set

namespace BanditRL.OnlineBregman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem divergence_extension_eq (X : Set E) (ψ φ : E → ℝ)
    (hEq : EqOn ψ φ X) (a b : E) (ha : a ∈ X) (hb : b ∈ interior X) :
    divergence ψ a b = divergence φ a b := by
  have he : Filter.EventuallyEq ψ φ (nhds b) :=
    (mem_interior_iff_mem_nhds.mp hb).mono fun z hz => hEq hz
  have hd : fderiv ℝ ψ b = fderiv ℝ φ b := he.fderiv_eq
  simp only [divergence, hEq ha, hEq (interior_subset hb), hd]

end BanditRL.OnlineBregman
