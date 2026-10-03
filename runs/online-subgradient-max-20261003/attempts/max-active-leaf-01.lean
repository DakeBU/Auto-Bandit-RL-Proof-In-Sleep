import BanditRLProof.OnlineSubgradientDifferentiability
import Mathlib.Data.Finset.Lattice.Fold
noncomputable section
open Set
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def SourceFiniteMax {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : EReal := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)

def SourceActiveSubgradientUnion {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : Set E :=
  {g | ∃ i, f i x = SourceFiniteMax f x ∧ g ∈ SourceSubdifferential (f i) x}

theorem active_subgradient_support_max
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (x : E) :
    SourceActiveSubgradientUnion f x ⊆ SourceSubdifferential (SourceFiniteMax f) x := by
  classical
  rintro g ⟨i, hi, hg⟩ y
  have hiy : f i y ≤ SourceFiniteMax f y :=
    Finset.le_sup' (fun j => f j y) (Finset.mem_univ i)
  rw [← hi]
  exact (hg y).trans hiy

#print axioms BanditRL.OnlineConvex.active_subgradient_support_max
end BanditRL.OnlineConvex
