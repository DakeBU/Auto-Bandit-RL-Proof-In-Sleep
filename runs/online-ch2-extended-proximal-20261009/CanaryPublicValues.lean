import Tests.OnlineBregmanExtendedCanary
open Set BanditRL.OnlineConvex BanditRL.OnlineBregman
namespace ExtendedCanaryAudit
theorem public_value_0 :
    let V : Set ℝ := Icc (-1) 1
    let f : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
    let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
    SourceProper f ∧
      (∀ z ∈ V, (SourceSubdifferential f z).Nonempty) ∧
      f 2 = ⊤ ∧
      ConvexOn ℝ V (fun z => (f z).toReal) ∧
      ¬ ConvexOn ℝ (univ : Set ℝ) (fun z => (f z).toReal) ∧
      StrictConvexOn ℝ univ ψ ∧
      IsMinOn (fun z => f z + ((divergence ψ z (1 / 2) : ℝ) : EReal)) V 0 ∧
      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
      divergence ψ (1 / 2) 0 = 9 / 64 ∧
      divergence ψ 0 (1 / 2) = 11 / 64 ∧
      (∀ u ∈ V, -|u| ≤ divergence ψ u (1 / 2) - divergence ψ u 0 - divergence ψ 0 (1 / 2)) ∧
      (-1 / 2 : ℝ) ≤ -5 / 16 :=
  BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic
#check BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic
#print axioms BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic
#print axioms public_value_0
theorem public_value_1 :
    let V : Set ℝ := Icc 0 1
    let f : ℝ → EReal := fun z => if z ∈ V then (z : EReal) else ⊤
    let ψ : ℝ → ℝ := fun z => z ^ 2 / 2
    SourceProper f ∧
      (∀ z ∈ V, (SourceSubdifferential f z).Nonempty) ∧
      f (-1) = ⊤ ∧
      (-1 : ℝ) ∉ V ∧
      ConvexOn ℝ V (fun z => (f z).toReal) ∧
      ¬ ConvexOn ℝ (univ : Set ℝ) (fun z => (f z).toReal) ∧
      StrictConvexOn ℝ univ ψ ∧
      IsMinOn (fun z => f z + ((divergence ψ z (-1) : ℝ) : EReal)) V 0 ∧
      divergence ψ 0 (-1) = 1 / 2 ∧
      (∀ u ∈ V, -u ≤ divergence ψ u (-1) - divergence ψ u 0 - divergence ψ 0 (-1)) ∧
      (-1 / 2 : ℝ) ≤ 1 / 2 :=
  BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center
#check BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center
#print axioms BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center
#print axioms public_value_1
end ExtendedCanaryAudit
