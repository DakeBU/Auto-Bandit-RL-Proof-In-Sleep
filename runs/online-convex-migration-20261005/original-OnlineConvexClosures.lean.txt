import BanditRLProof.OnlineConvexExamples

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem convex_comp_affine {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : F → EReal) (hf : IsConvexExtended f)
    (A : E →ᵃ[ℝ] F) : IsConvexExtended (fun x => f (A x)) := by
  have h := (show Convex ℝ (realEpigraph f) from hf).affine_preimage
    (A.prodMap (AffineMap.id ℝ ℝ))
  exact h

theorem convex_iSup {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ι → E → EReal) (hf : ∀ i, IsConvexExtended (f i)) :
    IsConvexExtended (fun x => ⨆ i, f i x) := by
  have he : realEpigraph (fun x => ⨆ i, f i x) = ⋂ i, realEpigraph (f i) := by
    ext p
    simp only [realEpigraph, mem_setOf_eq, mem_iInter, iSup_le_iff]
  change Convex ℝ (realEpigraph (fun x => ⨆ i, f i x))
  rw [he]
  exact convex_iInter hf

theorem convex_comp_monotone {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (g : ℝ → ℝ)
    (hf : IsConvexExtended (fun x => (f x : EReal)))
    (hg : IsConvexExtended (fun x => (g x : EReal))) (hmono : Monotone g) :
    IsConvexExtended (fun x => (g (f x) : EReal)) := by
  have hf' := (convexExtended_coe_iff f).mp hf
  have hg' := (convexExtended_coe_iff g).mp hg
  apply (convexExtended_coe_iff _).mpr
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (hmono (hf'.2 hx hy ha hb hab)).trans
    (hg'.2 (mem_univ _) (mem_univ _) ha hb hab)

end BanditRL.OnlineConvex
