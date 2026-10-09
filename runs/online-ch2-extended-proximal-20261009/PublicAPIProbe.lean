import BanditRLProof.OnlineBregmanExtended
open Set BanditRL.OnlineBregman
namespace OnlineBregmanExtendedAudit
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem public_value_0 (f : E → EReal) (V : Set E)
    (hV : Convex ℝ V) (hp : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ x ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f x).Nonempty) :
    ConvexOn ℝ V (fun x => (f x).toReal) :=
  BanditRL.OnlineBregman.finitePart_convex_of_subdifferentiable f V hV hp hs
#check BanditRL.OnlineBregman.finitePart_convex_of_subdifferentiable
#print BanditRL.OnlineBregman.finitePart_convex_of_subdifferentiable
#print axioms BanditRL.OnlineBregman.finitePart_convex_of_subdifferentiable
#print axioms public_value_0
end
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]
theorem public_value_1 (f : E → EReal) (V : Set E)
    (ψ : E → ℝ) (η : ℝ) (x p : E) (hp : p ∈ V)
    (hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥) :
    IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p ↔
      IsMinOn (fun z => (f z).toReal + η⁻¹ * divergence ψ z x) V p :=
  BanditRL.OnlineBregman.proximal_finitePart_minimizer_iff f V ψ η x p hp hfin
#check BanditRL.OnlineBregman.proximal_finitePart_minimizer_iff
#print BanditRL.OnlineBregman.proximal_finitePart_minimizer_iff
#print axioms BanditRL.OnlineBregman.proximal_finitePart_minimizer_iff
#print axioms public_value_1
end
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]
theorem public_value_2 (f : E → EReal) (V : Set E)
    (hV : Convex ℝ V) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (ψ : E → ℝ) (η : ℝ) (hη : 0 < η) (x p : E) (hp : p ∈ V)
    (hdx : DifferentiableAt ℝ ψ x) (hdp : DifferentiableAt ℝ ψ p)
    (hmin : IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p) :
    ∀ u ∈ V, η * ((f p).toReal - (f u).toReal) ≤
      divergence ψ u x - divergence ψ u p - divergence ψ p x :=
  BanditRL.OnlineBregman.proximal_one_step_extended f V hV hf hs ψ η hη x p hp hdx hdp hmin
#check BanditRL.OnlineBregman.proximal_one_step_extended
#print BanditRL.OnlineBregman.proximal_one_step_extended
#print axioms BanditRL.OnlineBregman.proximal_one_step_extended
#print axioms public_value_2
end
end OnlineBregmanExtendedAudit
