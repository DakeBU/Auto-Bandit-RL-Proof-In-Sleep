import BanditRLProof.OnlineBregmanProximal
import BanditRLProof.OnlineConvexOptimality
import BanditRLProof.OnlineSubgradientBasic

/-!
Finite-domain extended-real bridges for the required Chapter 2 prescient forward
dependency in Orabona v10. Global source supports produce finite values and real
convexity only on the feasible set. Values outside it may be positive infinity;
their total `toReal` values are never assumed to form a globally convex function.
The actual penalized minimum is transported using the shared finite-part order
theorem. These bridges do not prove attainment or construct a causal trajectory.
See `docs/contracts/online-ch2-extended-proximal-v1/stabilized-v1.json`.
-/

noncomputable section
open Set

namespace BanditRL.OnlineBregman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proper global supports at feasible points imply convexity of the finite part
on that set, with no global finite-part extension assumption. -/
theorem finitePart_convex_of_subdifferentiable (f : E → EReal) (V : Set E)
    (hV : Convex ℝ V) (hp : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ x ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f x).Nonempty) :
    ConvexOn ℝ V (fun x => (f x).toReal) := by
  have hfin : ∀ z ∈ V, f z = ((f z).toReal : EReal) := by
    intro z hz
    obtain ⟨g, hg⟩ := hs z hz
    have hzt := BanditRL.OnlineConvex.subgradient_point_finite f hp z g hg
    exact (EReal.coe_toReal (ne_of_lt hzt) (hp.1 z)).symm
  refine ⟨hV, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ V := hV hx hy ha hb hab
  obtain ⟨g, hg⟩ := hs z hz
  have h1 := hg x
  have h2 := hg y
  rw [hfin z hz, hfin x hx, ← EReal.coe_add] at h1
  rw [hfin z hz, hfin y hy, ← EReal.coe_add] at h2
  have h1r := EReal.coe_le_coe_iff.mp h1
  have h2r := EReal.coe_le_coe_iff.mp h2
  have hcancel : a * inner ℝ g (x - z) + b * inner ℝ g (y - z) = 0 := by
    dsimp [z]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    have he : b = 1 - a := by linarith
    rw [he]
    ring
  have h1w := mul_le_mul_of_nonneg_left h1r ha
  have h2w := mul_le_mul_of_nonneg_left h2r hb
  have hsum : a * (f z).toReal + b * (f z).toReal = (f z).toReal := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  change (f z).toReal ≤ a * (f x).toReal + b * (f y).toReal
  nlinarith only [h1w, h2w, hcancel, hsum]

variable [CompleteSpace E]

/-- Transport the actual EReal proximal minimum using only feasible finiteness.
Completeness is inherited from the reused shared minimum-order API. -/
theorem proximal_finitePart_minimizer_iff (f : E → EReal) (V : Set E)
    (ψ : E → ℝ) (η : ℝ) (x p : E) (hp : p ∈ V)
    (hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥) :
    IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p ↔
      IsMinOn (fun z => (f z).toReal + η⁻¹ * divergence ψ z x) V p := by
  let F : E → EReal := fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)
  have he : ∀ z ∈ V, F z = (((f z).toReal + η⁻¹ * divergence ψ z x : ℝ) : EReal) := by
    intro z hz
    change f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal) = _
    calc
      _ = ((f z).toReal : EReal) + ((η⁻¹ * divergence ψ z x : ℝ) : EReal) :=
        congrArg (fun v : EReal => v + ((η⁻¹ * divergence ψ z x : ℝ) : EReal))
          (EReal.coe_toReal (hfin z hz).1 (hfin z hz).2).symm
      _ = _ := (EReal.coe_add _ _).symm
  have hFfin : ∀ z ∈ V, F z ≠ ⊤ ∧ F z ≠ ⊥ := by
    intro z hz
    rw [he z hz]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hreal : ∀ z ∈ V, (F z).toReal = (f z).toReal + η⁻¹ * divergence ψ z x := by
    intro z hz
    rw [he z hz, EReal.toReal_coe]
  change IsMinOn F V p ↔ _
  refine (BanditRL.OnlineConvex.minOn_finitePart_iff F V p hp hFfin).trans ?_
  constructor
  · intro hm z hz
    have hh : (F p).toReal ≤ (F z).toReal := hm hz
    rw [hreal p hp, hreal z hz] at hh
    exact hh
  · intro hm z hz
    change (F p).toReal ≤ (F z).toReal
    rw [hreal p hp, hreal z hz]
    exact hm hz

/-- A true EReal proximal minimum gives the signed one-step comparison after
proper global supports justify every feasible finite loss value. -/
theorem proximal_one_step_extended (f : E → EReal) (V : Set E)
    (hV : Convex ℝ V) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (ψ : E → ℝ) (η : ℝ) (hη : 0 < η) (x p : E) (hp : p ∈ V)
    (hdx : DifferentiableAt ℝ ψ x) (hdp : DifferentiableAt ℝ ψ p)
    (hmin : IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p) :
    ∀ u ∈ V, η * ((f p).toReal - (f u).toReal) ≤
      divergence ψ u x - divergence ψ u p - divergence ψ p x := by
  have hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥ := by
    intro z hz
    obtain ⟨g, hg⟩ := hs z hz
    have hzt := BanditRL.OnlineConvex.subgradient_point_finite f hf z g hg
    exact ⟨ne_of_lt hzt, hf.1 z⟩
  have hc := finitePart_convex_of_subdifferentiable f V hV hf hs
  have hm := (proximal_finitePart_minimizer_iff f V ψ η x p hp hfin).mp hmin
  exact proximal_one_step V (fun z => (f z).toReal) ψ η hη x p hp hc hdx hdp hm

end BanditRL.OnlineBregman
