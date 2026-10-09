import BanditRLProof.OnlinePrescientBregman
open Set BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace PrescientTransitionAudit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem public_VALUE (V : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x0 x p : E) (t : ℕ)
    (hx : iterate V ψ η loss x0 t = some x)
    (hp : iterate V ψ η loss x0 (t + 1) = some p)
    (hη : 0 < η t) (hf : BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hdx : DifferentiableAt ℝ ψ x) (hdp : DifferentiableAt ℝ ψ p) :
    ∀ u ∈ V, η t * ((loss t p).toReal - (loss t u).toReal) ≤
      divergence ψ u x - divergence ψ u p - divergence ψ p x :=
  BanditRL.OnlinePrescientBregman.iterate_one_step V hV ψ η loss x0 x p t hx hp hη hf hs hdx hdp
#check @BanditRL.OnlinePrescientBregman.iterate_one_step
#print BanditRL.OnlinePrescientBregman.iterate_one_step
#print axioms BanditRL.OnlinePrescientBregman.iterate_one_step
#print axioms public_VALUE
end PrescientTransitionAudit
