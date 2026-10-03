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

#check Finset.exists_mem_eq_sup'
#check EReal.coe_le_coe_iff
#check isOpen_Iio.mem_nhds
#check mem_interior_iff_mem_nhds
#check Convex.inter
#check real_inner_smul_left
#check EReal.toReal_le_toReal
#check convexHull_min
end BanditRL.OnlineConvex
