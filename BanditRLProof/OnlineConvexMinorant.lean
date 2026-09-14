import BanditRLProof.OnlineConvexBarycenter
import BanditRLProof.OnlineConvexExtended
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Intrinsic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem affine_minorant_of_domain_interior (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥)
    (hf : IsConvexExtended f) (x : E) (hx : x ∈ interior (effectiveDomain f)) :
    ∃ (a : E →L[ℝ] ℝ) (b : ℝ), ∀ y, ((a y + b : ℝ) : EReal) ≤ f y := by
  classical
  have hxdom : x ∈ effectiveDomain f := interior_subset hx
  have hxfin := EReal.coe_toReal (ne_of_lt hxdom) (hbot x)
  let r : ℝ := (f x).toReal
  have hp : (x, r) ∈ realEpigraph f := by
    change f x ≤ ((f x).toReal : EReal)
    exact hxfin.ge
  have hpnot : (x, r) ∉ interior (realEpigraph f) := by
    intro hi
    have he : ∀ᶠ t : ℝ in 𝓝 r, (x, t) ∈ realEpigraph f :=
      (continuous_const.prodMk continuous_id).continuousAt.eventually
        (isOpen_interior.mem_nhds hi) |>.mono (fun t ht => interior_subset ht)
    have hm : IsLocalMin (fun t : ℝ => t) r := by
      filter_upwards [he] with t ht
      change r ≤ t
      change f x ≤ (t : EReal) at ht
      rw [← hxfin] at ht
      exact_mod_cast ht
    have hz := hm.hasDerivAt_eq_zero (hasDerivAt_id r)
    norm_num at hz
  obtain ⟨L, hL, hs⟩ := supporting_functional_at_closure (realEpigraph f) hf
    (x, r) (subset_closure hp) hpnot
  let A : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let c : ℝ := L (0, 1)
  have hsplit (y : E) (t : ℝ) : L (y, t) = A y + t * c := by
    change L (y, t) = L (y, 0) + t * L (0, 1)
    calc
      _ = L ((y, 0) + t • ((0 : E), (1 : ℝ))) := by simp
      _ = _ := by rw [map_add, map_smul]; rfl
  have hc0 : c ≤ 0 := by
    have hp1 : (x, r + 1) ∈ realEpigraph f := by
      change f x ≤ ((r + 1 : ℝ) : EReal)
      rw [← hxfin]
      exact_mod_cast (show r ≤ r + 1 by linarith)
    have hh := hs (x, r + 1) hp1
    rw [hsplit, hsplit] at hh
    linarith
  have hcne : c ≠ 0 := by
    intro hc
    have hm : IsMaxOn A (effectiveDomain f) x := by
      intro y hy
      have hyfin := EReal.coe_toReal (ne_of_lt hy) (hbot y)
      have hpy : (y, (f y).toReal) ∈ realEpigraph f := hyfin.ge
      have hh := hs (y, (f y).toReal) hpy
      rw [hsplit, hsplit, hc] at hh
      simpa using hh
    have hAz : A = 0 := (hm.isLocalMax (mem_interior_iff_mem_nhds.mp hx)).hasFDerivAt_eq_zero A.hasFDerivAt
    apply hL
    apply ContinuousLinearMap.ext
    intro p
    rcases p with ⟨y, t⟩
    rw [hsplit, hAz, hc]
    simp
  have hc : c < 0 := lt_of_le_of_ne hc0 hcne
  refine ⟨(-c⁻¹) • A, r + A x / c, ?_⟩
  intro y
  by_cases hy : f y = ⊤
  · simp [hy]
  · have hyfin := EReal.coe_toReal hy (hbot y)
    have hpy : (y, (f y).toReal) ∈ realEpigraph f := hyfin.ge
    have hh := hs (y, (f y).toReal) hpy
    rw [hsplit, hsplit] at hh
    have hb : (A x + r * c - A y) / c ≤ (f y).toReal :=
      (div_le_iff_of_neg hc).mpr (by linarith)
    have he : (-c⁻¹) * A y + (r + A x / c) = (A x + r * c - A y) / c := by
      field_simp
      ring
    change (((-c⁻¹) * A y + (r + A x / c) : ℝ) : EReal) ≤ f y
    rw [he, ← hyfin]
    exact_mod_cast hb

variable [MeasurableSpace E] [BorelSpace E]

theorem convex_affine_minorant (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hf : IsConvexExtended f) (hne : (effectiveDomain f).Nonempty) :
    ∃ (a : E →L[ℝ] ℝ) (b : ℝ), ∀ x, ((a x + b : ℝ) : EReal) ≤ f x := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    let S := affineSpan ℝ (effectiveDomain f)
    have hcv := convex_effectiveDomain f hf
    obtain ⟨x, hx⟩ := hne.intrinsicInterior hcv
    obtain ⟨p, hp, hpx⟩ := mem_intrinsicInterior.mp hx
    letI : Nonempty S := ⟨p⟩
    let e : S.direction ≃ᵃⁱ[ℝ] S := AffineIsometryEquiv.vaddConst ℝ p
    let T : S.direction →ᵃ[ℝ] E := S.subtype.comp e.toAffineEquiv.toAffineMap
    have hT (v : S.direction) : T v = (v : E) + (p : E) := rfl
    let F : S.direction → EReal := f ∘ T
    have hF : IsConvexExtended F := by
      exact hf.affine_preimage (T.prodMap (AffineMap.id ℝ ℝ))
    have hFi : (0 : S.direction) ∈ interior (effectiveDomain F) := by
      have hh : (0 : S.direction) ∈ e.toHomeomorph ⁻¹' interior ((↑) ⁻¹' effectiveDomain f : Set S) := by
        simpa [e] using hp
      rw [e.toHomeomorph.preimage_interior] at hh
      exact hh
    obtain ⟨a, b, hab⟩ := affine_minorant_of_domain_interior F (fun v => hbot (T v)) hF 0 hFi
    obtain ⟨g, hg⟩ := a.toLinearMap.exists_extend
    let G : E →L[ℝ] ℝ := g.toContinuousLinearMap
    refine ⟨G, b - G p, ?_⟩
    intro y
    by_cases hy : f y = ⊤
    · simp [hy]
    · have hyd : y ∈ effectiveDomain f := lt_top_iff_ne_top.mpr hy
      have hys : y ∈ S := subset_affineSpan ℝ _ hyd
      let v : S.direction := ⟨y - p, S.vsub_mem_direction hys p.property⟩
      have hTv : T v = y := by simp [hT, v]
      have hgv : G (v : E) = a v := congrArg (fun l : S.direction →ₗ[ℝ] ℝ => l v) hg
      have hh := hab v
      change ((a v + b : ℝ) : EReal) ≤ f (T v) at hh
      rw [hTv] at hh
      have hev : G y + (b - G p) = a v + b := by
        have hv : (v : E) = y - p := rfl
        rw [hv, map_sub] at hgv
        linarith
      rw [hev]
      exact hh

end BanditRL.OnlineConvex
