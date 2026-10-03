import BanditRLProof.Algorithms.HOOTree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Source A2 and Lemma 3 for general dissimilarities. No metric triangle
inequality, maximizer, or attainment of a regional supremum is assumed. -/
namespace BanditRLProof.HOO

def WeaklyLipschitz {X : Type*} (f : X → ℝ) (ell : X → X → ℝ) (best : ℝ) : Prop :=
  ∀ x y, best - f y ≤ best - f x + max (best - f x) (ell x y)

noncomputable def regionSup {X : Type*} (f : X → ℝ) (A : Set X) : ℝ := sSup (f '' A)

/-- First part of source Lemma 3, retaining the region's exact suboptimality. -/
theorem region_gap_le {X : Type*} (f : X → ℝ) (ell : X → X → ℝ)
    (best D : ℝ) (A : Set X) (hA : A.Nonempty)
    (hw : WeaklyLipschitz f ell best)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, ell x y ≤ D) (y : X) (hy : y ∈ A) :
    best - f y ≤ (best - regionSup f A) + max (best - regionSup f A) D := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨z, ⟨x, hx, rfl⟩, hfx⟩ := exists_lt_of_lt_csSup (hA.image f)
    (show regionSup f A - ε/2 < sSup (f '' A) by unfold regionSup; linarith)
  have hgap : best - f x ≤ best - regionSup f A + ε/2 := by linarith
  have hm : max (best - f x) (ell x y) ≤ max (best - regionSup f A) D + ε/2 := by
    apply max_le
    · have hh := le_max_left (best - regionSup f A) D
      linarith
    · have hh := (hdiam x hx y hy).trans (le_max_right (best - regionSup f A) D)
      linarith
  have hh := hw x y
  linarith

/-- Source Lemma 3, including c=0 and the max(2c,c+1) constant. -/
theorem near_optimal_region {X : Type*} (f : X → ℝ) (ell : X → X → ℝ)
    (best D c : ℝ) (A : Set X) (hA : A.Nonempty) (hD : 0 ≤ D)
    (hw : WeaklyLipschitz f ell best)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, ell x y ≤ D)
    (hgap : best - regionSup f A ≤ c*D) (y : X) (hy : y ∈ A) :
    best - f y ≤ max (2*c) (c+1)*D := by
  have h := region_gap_le f ell best D A hA hw hdiam y hy
  have hm := max_le_max_right D hgap
  have hid : c*D + max (c*D) D = max (2*c) (c+1)*D := by
    rw [max_mul_of_nonneg _ _ hD]
    rw [add_max]
    congr 1 <;> ring
  rw [← hid]
  exact h.trans (add_le_add hgap hm)

end BanditRLProof.HOO
