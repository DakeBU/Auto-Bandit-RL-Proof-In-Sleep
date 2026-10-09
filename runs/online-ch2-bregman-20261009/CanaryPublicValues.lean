import Tests.OnlineBregmanProximalCanary
open Set BanditRL.OnlineBregman
namespace OnlineBregmanCanaryAudit
theorem public_value_0 :
    StrictConvexOn ℝ univ (fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2) ∧
      IsMinOn (fun z : ℝ => |z| + divergence (fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2) z (1 / 2)) univ 0 ∧
      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
      divergence (fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2) (1 / 2) 0 = 9 / 64 ∧
      divergence (fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2) 0 (1 / 2) = 11 / 64 ∧
      (∀ u : ℝ, -|u| ≤ divergence (fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2) u (1 / 2) -
        divergence (fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2) u 0 - divergence (fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2) 0 (1 / 2)) ∧
      (-1 / 2 : ℝ) ≤ -5 / 16 :=
  BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth
#check BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth
#print axioms BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth
#print axioms public_value_0
theorem public_value_1 :
    StrictConvexOn ℝ univ (fun z : ℝ => z ^ 2 / 2) ∧
      (-1 : ℝ) ∉ Icc 0 1 ∧
      IsMinOn (fun z : ℝ => |z| + divergence (fun z : ℝ => z ^ 2 / 2) z (-1)) (Icc 0 1) 0 ∧
      divergence (fun z : ℝ => z ^ 2 / 2) 0 (-1) = 1 / 2 ∧
      (∀ u ∈ Icc (0 : ℝ) 1, -|u| ≤ divergence (fun z : ℝ => z ^ 2 / 2) u (-1) -
        divergence (fun z : ℝ => z ^ 2 / 2) u 0 - divergence (fun z : ℝ => z ^ 2 / 2) 0 (-1)) ∧
      (-1 / 2 : ℝ) ≤ 1 / 2 :=
  BanditRL.OnlineBregmanCanary.boundary_outside_initial
#check BanditRL.OnlineBregmanCanary.boundary_outside_initial
#print axioms BanditRL.OnlineBregmanCanary.boundary_outside_initial
#print axioms public_value_1
end OnlineBregmanCanaryAudit
