import BanditRLProof.OnlinePrescientBregman
open Set BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace PrescientRecursionAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem public_VALUE_iterate_prefix (V : Set E) (ψ : E → ℝ) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x0 : E) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s) :
    iterate V ψ η loss x0 t = iterate V ψ η' loss' x0 t :=
  BanditRL.OnlinePrescientBregman.iterate_prefix V ψ η η' loss loss' x0 t hη hloss
#check BanditRL.OnlinePrescientBregman.iterate_prefix
#print BanditRL.OnlinePrescientBregman.iterate_prefix
#print axioms BanditRL.OnlinePrescientBregman.iterate_prefix
#print axioms public_VALUE_iterate_prefix
theorem public_VALUE_iterate_succ_some_spec (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 p : E) (t : ℕ)
    (h : iterate V ψ η loss x0 (t + 1) = some p) :
    ∃ x, iterate V ψ η loss x0 t = some x ∧ p ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z x : ℝ) : EReal)) V p :=
  BanditRL.OnlinePrescientBregman.iterate_succ_some_spec V ψ η loss x0 p t h
#check BanditRL.OnlinePrescientBregman.iterate_succ_some_spec
#print BanditRL.OnlinePrescientBregman.iterate_succ_some_spec
#print axioms BanditRL.OnlinePrescientBregman.iterate_succ_some_spec
#print axioms public_VALUE_iterate_succ_some_spec
theorem public_VALUE_iterate_no_recovery (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (t k : ℕ)
    (h : iterate V ψ η loss x0 t = none) :
    iterate V ψ η loss x0 (t + k) = none :=
  BanditRL.OnlinePrescientBregman.iterate_no_recovery V ψ η loss x0 t k h
#check BanditRL.OnlinePrescientBregman.iterate_no_recovery
#print BanditRL.OnlinePrescientBregman.iterate_no_recovery
#print axioms BanditRL.OnlinePrescientBregman.iterate_no_recovery
#print axioms public_VALUE_iterate_no_recovery
theorem public_VALUE_iterate_complete_of_step_attained (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (T : ℕ)
    (hatt : ∀ t < T, ∀ x, iterate V ψ η loss x0 t = some x →
      ∃ p, p ∈ V ∧
        IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z x : ℝ) : EReal)) V p) :
    ∃ p, iterate V ψ η loss x0 T = some p :=
  BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained V ψ η loss x0 T hatt
#check BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained
#print BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained
#print axioms BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained
#print axioms public_VALUE_iterate_complete_of_step_attained
end PrescientRecursionAudit
