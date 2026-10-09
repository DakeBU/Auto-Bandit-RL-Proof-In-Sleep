import BanditRLProof.OnlinePrescientBregman
open Set BanditRL.OnlineBregman
namespace PrescientLocalityAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem public_VALUE (X : Set E) (ψ φ : E → ℝ)
    (hEq : EqOn ψ φ X) (a b : E) (ha : a ∈ X) (hb : b ∈ interior X) :
    divergence ψ a b = divergence φ a b :=
  BanditRL.OnlineBregman.divergence_extension_eq X ψ φ hEq a b ha hb
#check BanditRL.OnlineBregman.divergence_extension_eq
#print BanditRL.OnlineBregman.divergence_extension_eq
#print axioms BanditRL.OnlineBregman.divergence_extension_eq
#print axioms public_VALUE
end PrescientLocalityAudit
