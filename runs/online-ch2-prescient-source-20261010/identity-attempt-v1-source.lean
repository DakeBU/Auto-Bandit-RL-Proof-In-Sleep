import BanditRLProof.OnlinePrescientBregmanRegret

/-!
Source-domain/properness and unique-update transports for the required Chapter2
prescient forward dependency in Orabona v10, Algorithm15.8/Theorem15.30.
The source guarantee concerns valid interior argmin runs. Closedness and strict
convexity are not universal attainment assumptions; the existing exponential
counterexample and Option failure boundary remain in force. Source wrappers
retain literal finite-dimensional/closedness premises. The same shared loss,
divergence, selector and recursion are reused. No new per-Book project.
See docs/contracts/online-ch2-prescient-source-v1/stabilized-v1.json.
-/

noncomputable section
open Set Finset
open BanditRL.OnlineBregman
set_option autoImplicit false

namespace BanditRL.OnlineConvex
variable {E : Type*}

theorem sourceProper_of_domain (f : E → EReal) (V : Set E)
    (hV : V.Nonempty) (hbot : ∀ z, f z ≠ ⊥)
    (hdom : V ⊆ effectiveDomain f) :
    SourceProper f := by
  refine ⟨hbot, ?_⟩
  obtain ⟨z, hz⟩ := hV
  exact ⟨z, (f z).toReal, (EReal.coe_toReal (ne_of_lt (hdom hz)) (hbot z)).symm⟩

end BanditRL.OnlineConvex

namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem penalized_strictConvex (V X : Set E) (hV : Convex ℝ V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (f : E → EReal) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (η : ℝ) (hη : 0 < η) (x : E) :
    StrictConvexOn ℝ V (fun z => (f z).toReal + η⁻¹ * divergence ψ z x) := by
  have hc := finitePart_convex_of_subdifferentiable f V hV hf hs
  refine ⟨hV, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  have hfc := hc.2 hp hq ha.le hb.le hab
  have hψs := hψ.2 (hVX hp) (hVX hq) hpq ha hb hab
  simp only [smul_eq_mul] at hfc hψs ⊢
  have hlinear : fderiv ℝ ψ x (a • p + b • q - x) =
      a * fderiv ℝ ψ x (p - x) + b * fderiv ℝ ψ x (q - x) := by
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    have he : b = 1 - a := by linarith only [hab]
    rw [he]
    ring
  have hD : divergence ψ (a • p + b • q) x <
      a * divergence ψ p x + b * divergence ψ q x := by
    unfold divergence
    rw [hlinear]
    have hconst : (a + b) * ψ x = ψ x := by rw [hab, one_mul]
    nlinarith only [hψs, hconst]
  have hweighted := mul_lt_mul_of_pos_left hD (inv_pos.mpr hη)
  nlinarith only [hfc, hweighted]

end BanditRL.OnlinePrescientBregman

namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem advance_eq_some_of_minimizer (V X : Set E) (hV : Convex ℝ V)
    (hVX : V ⊆ X) (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (f : E → EReal) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (η : ℝ) (hη : 0 < η) (x p : E) (hp : p ∈ V)
    (hmin : IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p) :
    advance V ψ η f x = some p := by
  classical
  have hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥ := by
    intro z hz
    obtain ⟨g, hg⟩ := hs z hz
    exact ⟨ne_of_lt (BanditRL.OnlineConvex.subgradient_point_finite f hf z g hg), hf.1 z⟩
  have hstrict := penalized_strictConvex V X hV hVX ψ hψ f hf hs η hη x
  have hpReal := (proximal_finitePart_minimizer_iff f V ψ η x p hp hfin).mp hmin
  have hatt : ∃ q, q ∈ V ∧
      IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V q :=
    ⟨p, hp, hmin⟩
  have hq := Classical.choose_spec hatt
  have hqReal := (proximal_finitePart_minimizer_iff f V ψ η x
    (Classical.choose hatt) hq.1 hfin).mp hq.2
  have heq : Classical.choose hatt = p := hstrict.eq_of_isMinOn hqReal hpReal hq.1 hp
  unfold advance
  rw [dif_pos hatt]
  exact congrArg some heq

end BanditRL.OnlinePrescientBregman

namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem iterate_eq_of_source_updates (V X : Set E) (hV : Convex ℝ V)
    (hVX : V ⊆ X) (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hinit : x 0 = x0) (hη : ∀ t < T, 0 < η t)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1))) :
    ∀ t ≤ T, iterate V ψ η loss x0 t = some (x t) := by
  intro t
  induction t with
  | zero =>
      intro _
      simp only [iterate, hinit]
  | succ t ih =>
      intro ht
      have hlt : t < T := Nat.lt_of_succ_le ht
      have hprev : t ≤ T := Nat.le_of_lt hlt
      change (iterate V ψ η loss x0 t).bind (advance V ψ (η t) (loss t)) =
        some (x (t + 1))
      rw [ih hprev]
      simp only [Option.bind_some]
      exact advance_eq_some_of_minimizer V X hV hVX ψ hψ (loss t)
        (hf t hlt) (hs t hlt) (η t) (hη t hlt) (x t) (x (t + 1))
        (hmin t hlt).1 (hmin t hlt).2

end BanditRL.OnlinePrescientBregman
