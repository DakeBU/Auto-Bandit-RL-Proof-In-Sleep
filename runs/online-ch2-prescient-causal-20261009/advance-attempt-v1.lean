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
  · have he := Option.some.inj h
    exact he ▸ Classical.choose_spec hatt
  · cases h

theorem advance_none_iff (V : Set E) (ψ : E → ℝ) (η : ℝ)
    (f : E → EReal) (x : E) :
    advance V ψ η f x = none ↔ ¬ ∃ p, p ∈ V ∧
      IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p := by
  classical
  unfold advance
  split_ifs with hatt <;> simp [hatt]

end BanditRL.OnlinePrescientBregman
