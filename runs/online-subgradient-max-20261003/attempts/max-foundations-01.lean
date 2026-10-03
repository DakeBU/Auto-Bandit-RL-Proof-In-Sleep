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



theorem finiteMax_attained {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : ∃ i, SourceFiniteMax f x = f i x := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => f i x)
  exact ⟨i, he⟩

theorem finiteMax_point_finite {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (hp : ∀ i, SourceProper (f i))
    (x : E) (hx : ∀ i, x ∈ effectiveDomain (f i)) :
    ∃ a : ℝ, SourceFiniteMax f x = (a : EReal) := by
  obtain ⟨i, hi⟩ := finiteMax_attained f x
  exact ⟨(f i x).toReal, hi.trans (EReal.coe_toReal (ne_of_lt (hx i)) ((hp i).1 x)).symm⟩

theorem subgradient_iff_real_support (f : E → EReal)
    (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ effectiveDomain f) (g : E) :
    g ∈ SourceSubdifferential f x ↔
      ∀ y, f y ≠ ⊤ → (f x).toReal + inner ℝ g (y - x) ≤ (f y).toReal := by
  have hxf := EReal.coe_toReal (ne_of_lt hx) (hbot x)
  constructor
  · intro hg y hyt
    have hyf := EReal.coe_toReal hyt (hbot y)
    have hi := hg y
    rw [← hxf, ← hyf, ← EReal.coe_add] at hi
    exact EReal.coe_le_coe_iff.mp hi
  · intro hg y
    by_cases hyt : f y = ⊤
    · rw [hyt]
      exact le_top
    · have hyf := EReal.coe_toReal hyt (hbot y)
      change f x + (inner ℝ g (y - x) : EReal) ≤ f y
      rw [← hxf, ← hyf, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (hg y hyt)

theorem convex_sourceSubdifferential (f : E → EReal)
    (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ effectiveDomain f) :
    Convex ℝ (SourceSubdifferential f x) := by
  intro g hg k hk a b ha hb hab
  rw [subgradient_iff_real_support f hbot x hx] at hg hk ⊢
  intro y hyt
  have h1 := mul_le_mul_of_nonneg_left (hg y hyt) ha
  have h2 := mul_le_mul_of_nonneg_left (hk y hyt) hb
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith

theorem continuousAt_mem_domain_interior (f : E → EReal) (x : E)
    (hx : x ∈ effectiveDomain f) (hc : ContinuousAt f x) :
    x ∈ interior (effectiveDomain f) := by
  apply mem_interior_iff_mem_nhds.mpr
  exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds hx)

#print axioms BanditRL.OnlineConvex.finiteMax_attained
#print axioms BanditRL.OnlineConvex.finiteMax_point_finite
#print axioms BanditRL.OnlineConvex.subgradient_iff_real_support
#print axioms BanditRL.OnlineConvex.convex_sourceSubdifferential
#print axioms BanditRL.OnlineConvex.continuousAt_mem_domain_interior
end BanditRL.OnlineConvex
