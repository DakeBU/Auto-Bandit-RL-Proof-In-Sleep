import BanditRLProof.OnlineBregmanProximal
open Set BanditRL.OnlineBregman
namespace OnlineBregmanAudit
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem public_value_0 (ψ : E → ℝ) (x : E) :
    divergence ψ x x = 0 :=
  BanditRL.OnlineBregman.divergence_self ψ x
#check BanditRL.OnlineBregman.divergence_self
#print BanditRL.OnlineBregman.divergence_self
#print axioms BanditRL.OnlineBregman.divergence_self
#print axioms public_value_0
end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem public_value_1 (ψ : E → ℝ) (x y z : E) :
    divergence ψ z x + divergence ψ x y - divergence ψ z y =
      (fderiv ℝ ψ y - fderiv ℝ ψ x) (z - x) :=
  BanditRL.OnlineBregman.three_point_identity ψ x y z
#check BanditRL.OnlineBregman.three_point_identity
#print BanditRL.OnlineBregman.three_point_identity
#print axioms BanditRL.OnlineBregman.three_point_identity
#print axioms public_value_1
end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem public_value_2 (X : Set E) (ψ : E → ℝ) (hψ : ConvexOn ℝ X ψ)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) (hd : DifferentiableAt ℝ ψ y) :
    0 ≤ divergence ψ x y :=
  BanditRL.OnlineBregman.divergence_nonneg X ψ hψ x y hx hy hd
#check BanditRL.OnlineBregman.divergence_nonneg
#print BanditRL.OnlineBregman.divergence_nonneg
#print axioms BanditRL.OnlineBregman.divergence_nonneg
#print axioms public_value_2
end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem public_value_3 (V : Set E) (f ψ : E → ℝ) (η : ℝ) (hη : 0 < η)
    (x p : E) (hp : p ∈ V) (hf : ConvexOn ℝ V f)
    (hdx : DifferentiableAt ℝ ψ x) (hdp : DifferentiableAt ℝ ψ p)
    (hmin : IsMinOn (fun z => f z + η⁻¹ * divergence ψ z x) V p) :
    ∀ u ∈ V, η * (f p - f u) ≤
      divergence ψ u x - divergence ψ u p - divergence ψ p x :=
  BanditRL.OnlineBregman.proximal_one_step V f ψ η hη x p hp hf hdx hdp hmin
#check BanditRL.OnlineBregman.proximal_one_step
#print BanditRL.OnlineBregman.proximal_one_step
#print axioms BanditRL.OnlineBregman.proximal_one_step
#print axioms public_value_3
end
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem public_value_4 (ψ : E → ℝ) (x y : E)
    (hd : DifferentiableAt ℝ ψ y) :
    divergence ψ x y = ψ x - ψ y - inner ℝ (gradient ψ y) (x - y) :=
  BanditRL.OnlineBregman.divergence_eq_gradient ψ x y hd
#check BanditRL.OnlineBregman.divergence_eq_gradient
#print BanditRL.OnlineBregman.divergence_eq_gradient
#print axioms BanditRL.OnlineBregman.divergence_eq_gradient
#print axioms public_value_4
end
end OnlineBregmanAudit
