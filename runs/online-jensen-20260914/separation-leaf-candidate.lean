import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open Set
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem supporting_functional_at_closure (s : Set E) (hs : Convex ℝ s)
    (x : E) (hx : x ∈ closure s) (hxi : x ∉ interior s) :
    ∃ a : E →L[ℝ] ℝ, a ≠ 0 ∧ ∀ y ∈ s, a y ≤ a x := by
  by_cases hint : (interior s).Nonempty
  · exact geometric_hahn_banach_of_nonempty_interior_point hs hxi hint
  · let A := affineSpan ℝ s
    have hA : A ≠ ⊤ := fun h => hint (hs.interior_nonempty_iff_affineSpan_eq_top.mpr h)
    have hxA : x ∈ A := closure_minimal (subset_affineSpan ℝ s) A.closed_of_finiteDimensional hx
    have hdir : A.direction < ⊤ := lt_top_iff_ne_top.mpr fun h =>
      hA ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x, hxA⟩).mp h)
    obtain ⟨a, hane, ha⟩ := A.direction.exists_le_ker_of_lt_top hdir
    refine ⟨a.toContinuousLinearMap, ?_, ?_⟩
    · intro hz
      exact hane (congrArg ContinuousLinearMap.toLinearMap hz)
    · intro y hy
      have hxy : y - x ∈ A.direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ s hy) hxA
      have hz : a (y - x) = 0 := ha hxy
      rw [map_sub] at hz
      change a y ≤ a x
      exact (sub_eq_zero.mp hz).le

end BanditRL.OnlineConvex
