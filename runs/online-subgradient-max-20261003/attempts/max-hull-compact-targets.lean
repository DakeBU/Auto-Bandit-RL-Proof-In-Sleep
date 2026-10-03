import BanditRLProof.OnlineSubgradientDifferentiability
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.Convex.Join
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

theorem isCompact_convexJoin (s t : Set E) (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  -- Parser-only unproved slot.
theorem isCompact_convexHull_finite_convex_union {ι : Type*}
    (s : ι → Set E) (F : Finset ι)
    (hc : ∀ i ∈ F, Convex ℝ (s i)) (hk : ∀ i ∈ F, IsCompact (s i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ F, s i)) := by
  -- Parser-only unproved slot.
end BanditRL.OnlineConvex
