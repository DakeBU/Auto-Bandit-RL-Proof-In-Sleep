import BanditRLProof.OnlinePrescientBregman
open Set BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace PrescientAdvanceAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem public_VALUE_advance_some_spec (V : Set E) (ψ : E → ℝ) (η : ℝ)
    (f : E → EReal) (x p : E) (h : advance V ψ η f x = some p) :
    p ∈ V ∧ IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p :=
  BanditRL.OnlinePrescientBregman.advance_some_spec V ψ η f x p h
#check BanditRL.OnlinePrescientBregman.advance_some_spec
#print BanditRL.OnlinePrescientBregman.advance_some_spec
#print axioms BanditRL.OnlinePrescientBregman.advance_some_spec
#print axioms public_VALUE_advance_some_spec
theorem public_VALUE_advance_none_iff (V : Set E) (ψ : E → ℝ) (η : ℝ)
    (f : E → EReal) (x : E) :
    advance V ψ η f x = none ↔ ¬ ∃ p, p ∈ V ∧
      IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p :=
  BanditRL.OnlinePrescientBregman.advance_none_iff V ψ η f x
#check BanditRL.OnlinePrescientBregman.advance_none_iff
#print BanditRL.OnlinePrescientBregman.advance_none_iff
#print axioms BanditRL.OnlinePrescientBregman.advance_none_iff
#print axioms public_VALUE_advance_none_iff
#print BanditRL.OnlinePrescientBregman.advance
#print axioms BanditRL.OnlinePrescientBregman.advance
#print BanditRL.OnlinePrescientBregman.iterate
#print axioms BanditRL.OnlinePrescientBregman.iterate
end PrescientAdvanceAudit
