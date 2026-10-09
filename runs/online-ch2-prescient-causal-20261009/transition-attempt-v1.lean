import BanditRLProof.OnlineBregmanExtended
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Data.Option.Basic

noncomputable section
open Set

namespace BanditRL.OnlineBregman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem divergence_extension_eq (X : Set E) (ψ φ : E → ℝ)
    (hEq : EqOn ψ φ X) (a b : E) (ha : a ∈ X) (hb : b ∈ interior X) :
    divergence ψ a b = divergence φ a b := by
  have hX : Filter.Eventually (fun z => z ∈ X) (nhds b) :=
    mem_interior_iff_mem_nhds.mp hb
  have he : Filter.EventuallyEq (nhds b) ψ φ :=
    hX.mono fun z hz => hEq hz
  have hd : fderiv ℝ ψ b = fderiv ℝ φ b := he.fderiv_eq
  simp only [divergence, hEq ha, hEq (interior_subset hb), hd]

end BanditRL.OnlineBregman

namespace BanditRL.OnlinePrescientBregman
open BanditRL.OnlineBregman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def advance (V : Set E) (ψ : E → ℝ) (η : ℝ) (f : E → EReal) (x : E) : Option E := by
  classical
  exact if h : ∃ p, p ∈ V ∧
      IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p
    then some (Classical.choose h) else none

def iterate (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) : ℕ → Option E
  | 0 => some x0
  | t + 1 => (iterate V ψ η loss x0 t).bind (advance V ψ (η t) (loss t))

theorem advance_some_spec (V : Set E) (ψ : E → ℝ) (η : ℝ)
    (f : E → EReal) (x p : E) (h : advance V ψ η f x = some p) :
    p ∈ V ∧ IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p := by
  classical
  unfold advance at h
  split_ifs at h with hatt
  have he := Option.some.inj h
  exact he ▸ Classical.choose_spec hatt

theorem advance_none_iff (V : Set E) (ψ : E → ℝ) (η : ℝ)
    (f : E → EReal) (x : E) :
    advance V ψ η f x = none ↔ ¬ ∃ p, p ∈ V ∧
      IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p := by
  classical
  unfold advance
  split_ifs with hatt
  · constructor
    · intro h
      cases h
    · intro h
      exact (h hatt).elim
  · exact ⟨fun _ => hatt, fun _ => rfl⟩

theorem iterate_prefix (V : Set E) (ψ : E → ℝ) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x0 : E) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s) :
    iterate V ψ η loss x0 t = iterate V ψ η' loss' x0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [iterate]
      rw [ih (fun s hs => hη s (Nat.lt_succ_of_lt hs))
        (fun s hs => hloss s (Nat.lt_succ_of_lt hs)),
        hη t (Nat.lt_succ_self t), hloss t (Nat.lt_succ_self t)]

theorem iterate_succ_some_spec (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 p : E) (t : ℕ)
    (h : iterate V ψ η loss x0 (t + 1) = some p) :
    ∃ x, iterate V ψ η loss x0 t = some x ∧ p ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z x : ℝ) : EReal)) V p := by
  change (iterate V ψ η loss x0 t).bind (advance V ψ (η t) (loss t)) = some p at h
  obtain ⟨x, hx, hstep⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨x, hx, advance_some_spec V ψ (η t) (loss t) x p hstep⟩

theorem iterate_no_recovery (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (t k : ℕ)
    (h : iterate V ψ η loss x0 t = none) :
    iterate V ψ η loss x0 (t + k) = none := by
  induction k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
      change (iterate V ψ η loss x0 (t + k)).bind
        (advance V ψ (η (t + k)) (loss (t + k))) = none
      rw [ih]
      rfl

theorem iterate_complete_of_step_attained (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (T : ℕ)
    (hatt : ∀ t < T, ∀ x, iterate V ψ η loss x0 t = some x →
      ∃ p, p ∈ V ∧
        IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z x : ℝ) : EReal)) V p) :
    ∃ p, iterate V ψ η loss x0 T = some p := by
  induction T with
  | zero => exact ⟨x0, rfl⟩
  | succ T ih =>
      obtain ⟨x, hx⟩ := ih (fun t ht y hy => hatt t (Nat.lt_succ_of_lt ht) y hy)
      have ha := hatt T (Nat.lt_succ_self T) x hx
      have hn : advance V ψ (η T) (loss T) x ≠ none := by
        intro hnone
        exact (advance_none_iff V ψ (η T) (loss T) x).mp hnone ha
      cases hs : advance V ψ (η T) (loss T) x with
      | none => exact (hn hs).elim
      | some p =>
          refine ⟨p, ?_⟩
          change (iterate V ψ η loss x0 T).bind
            (advance V ψ (η T) (loss T)) = some p
          rw [hx]
          exact hs


section InnerProduct
variable [InnerProductSpace ℝ E] [CompleteSpace E]

theorem iterate_one_step (V : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x0 x p : E) (t : ℕ)
    (hx : iterate V ψ η loss x0 t = some x)
    (hp : iterate V ψ η loss x0 (t + 1) = some p)
    (hη : 0 < η t) (hf : BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hdx : DifferentiableAt ℝ ψ x) (hdp : DifferentiableAt ℝ ψ p) :
    ∀ u ∈ V, η t * ((loss t p).toReal - (loss t u).toReal) ≤
      divergence ψ u x - divergence ψ u p - divergence ψ p x := by
  obtain ⟨y, hy, hpV, hm⟩ := iterate_succ_some_spec V ψ η loss x0 p t hp
  have he : y = x := Option.some.inj (hy.symm.trans hx)
  subst y
  exact proximal_one_step_extended (loss t) V hV hf hs ψ (η t) hη x p hpV hdx hdp hm

end InnerProduct
end BanditRL.OnlinePrescientBregman
