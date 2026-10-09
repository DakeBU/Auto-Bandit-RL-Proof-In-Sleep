import Tests.OnlinePrescientBregmanCanary
open Set BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace PrescientBoundaryAudit
theorem public_VALUE_closed_strict_regularizer_missing_minimum :
    let V : Set ℝ := Iic 0
    let f : ℝ → EReal := fun z => (z : EReal)
    let ψ : ℝ → ℝ := Real.exp
    V.Nonempty ∧ IsClosed V ∧ Convex ℝ V ∧ (0 : ℝ) ∈ V ∧
      SourceProper f ∧
      (∀ z : ℝ, (SourceSubdifferential f z).Nonempty) ∧
      SourceClosed (fun z => ((ψ z : ℝ) : EReal)) ∧
      StrictConvexOn ℝ univ ψ ∧
      (∀ z : ℝ, DifferentiableAt ℝ ψ z) ∧
      (0 : ℝ) ∈ interior (univ : Set ℝ) ∧
      (∀ z : ℝ, f z + ((divergence ψ z 0 : ℝ) : EReal) = ((Real.exp z - 1 : ℝ) : EReal)) ∧
      (¬ ∃ p, p ∈ V ∧ IsMinOn (fun z => f z + ((divergence ψ z 0 : ℝ) : EReal)) V p) ∧
      advance V ψ 1 f 0 = none ∧
      (∀ k : ℕ, iterate V ψ (fun _ => 1) (fun _ => f) 0 (k + 1) = none) :=
  BanditRL.OnlinePrescientBregmanCanary.closed_strict_regularizer_missing_minimum
#print BanditRL.OnlinePrescientBregmanCanary.closed_strict_regularizer_missing_minimum
#print axioms BanditRL.OnlinePrescientBregmanCanary.closed_strict_regularizer_missing_minimum
#print axioms public_VALUE_closed_strict_regularizer_missing_minimum
theorem public_VALUE_interior_extension_boundary_difference :
    let X : Set ℝ := Ici 0
    let ψ : ℝ → ℝ := fun z => z ^ 2 + z
    let φ : ℝ → ℝ := fun z => z ^ 2 + |z|
    EqOn ψ φ X ∧ ψ (-1) ≠ φ (-1) ∧ (1 : ℝ) ∈ interior X ∧ (2 : ℝ) ∈ X ∧
      divergence ψ 2 1 = divergence φ 2 1 ∧ divergence ψ 2 1 = 1 ∧
      divergence ψ 2 0 = 4 ∧ divergence φ 2 0 = 6 ∧ ¬ DifferentiableAt ℝ φ 0 :=
  BanditRL.OnlinePrescientBregmanCanary.interior_extension_boundary_difference
#print BanditRL.OnlinePrescientBregmanCanary.interior_extension_boundary_difference
#print axioms BanditRL.OnlinePrescientBregmanCanary.interior_extension_boundary_difference
#print axioms public_VALUE_interior_extension_boundary_difference
end PrescientBoundaryAudit
