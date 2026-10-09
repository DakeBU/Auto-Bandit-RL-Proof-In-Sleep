import Tests.OnlineProximalComparisonCanary

open Set

namespace OnlineProximalCanaryAudit

theorem nonsmooth_shifted_quadratic_value :
    IsMinOn (fun z : ℝ => |z| + (z - 1 / 2) ^ 2 / 2) univ 0 ∧
      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
      (∀ u : ℝ, -|u| ≤ -u / 2) ∧
      (-1 / 4 : ℝ) ≤ -1 / 8 := by
  exact BanditRL.OnlineProximalCanary.nonsmooth_shifted_quadratic

#check BanditRL.OnlineProximalCanary.nonsmooth_shifted_quadratic

#print axioms BanditRL.OnlineProximalCanary.nonsmooth_shifted_quadratic

#print axioms nonsmooth_shifted_quadratic_value

theorem boundary_linear_regularizer_value :
    IsMinOn (fun z : ℝ => z + (-z / 2)) (Icc 0 1) 0 ∧
      (∀ u ∈ Icc (0 : ℝ) 1, -u ≤ -u / 2) ∧
      ¬ IsMinOn (fun z : ℝ => z + (-z / 2)) univ 0 := by
  exact BanditRL.OnlineProximalCanary.boundary_linear_regularizer

#check BanditRL.OnlineProximalCanary.boundary_linear_regularizer

#print axioms BanditRL.OnlineProximalCanary.boundary_linear_regularizer

#print axioms boundary_linear_regularizer_value

theorem nonconvex_regularizer_value :
    IsMinOn (fun z : ℝ => z ^ 2 + (-z ^ 2 / 2 + z)) univ (-1) ∧
      ¬ ConvexOn ℝ univ (fun z : ℝ => -z ^ 2 / 2 + z) ∧
      (∀ u : ℝ, 1 - u ^ 2 ≤ 2 * (u + 1)) ∧
      (1 : ℝ) ≤ 2 := by
  exact BanditRL.OnlineProximalCanary.nonconvex_regularizer

#check BanditRL.OnlineProximalCanary.nonconvex_regularizer

#print axioms BanditRL.OnlineProximalCanary.nonconvex_regularizer

#print axioms nonconvex_regularizer_value

end OnlineProximalCanaryAudit
