import BanditRLProof
import Tests.OnlineGradientDescentCanary

noncomputable section
open Set Finset
open BanditRL.OnlineGradientDescent
open Tests.OnlineGradientDescent

namespace Tests.OnlineGradientDescentVariable

def rates (t : ℕ) : ℝ := if t = 0 then 1 else 1 / 2

lemma first_point : iterateVariable interval rates losses 0 1 = 1 := by
  simp only [iterateVariable, step, gradient_losses]
  norm_num [rates]
  exact project_high

lemma second_point : iterateVariable interval rates losses 0 2 = 3 / 4 := by
  change step interval (rates 1) (losses 1) (iterateVariable interval rates losses 0 1) = _
  rw [first_point]
  simp only [step, gradient_losses]
  norm_num [rates]
  apply project_eq_of_variational interval (3 / 4) (3 / 4) (by norm_num [interval])
  intro w hw
  simp

/-- Strictly decreasing steps, changing losses, active first projection, nonzero terminal residual. -/
theorem nondegenerate : rates 1 < rates 0 ∧
    iterateVariable interval rates losses 0 1 = 1 ∧
    iterateVariable interval rates losses 0 2 = 3 / 4 ∧
    regretVariable interval rates losses 0 0 2 = 1 / 2 ∧
    ‖iterateVariable interval rates losses 0 2 - (0 : ℝ)‖ ^ 2 = 9 / 16 := by
  refine ⟨by norm_num [rates], first_point, second_point, ?_, ?_⟩
  · simp only [regretVariable, sum_range_succ, sum_range_zero, zero_add]
    rw [first_point]
    norm_num [iterateVariable, losses]
  · rw [second_point]
    norm_num

/-- Use the public exact finite-diameter endpoint on the same concrete trajectory. -/
example : regretVariable interval rates losses 0 0 2 ≤
    (Metric.diam interval.carrier) ^ 2 / (2 * rates (2 - 1)) +
      (∑ t ∈ range 2, rates t / 2 * ‖gradient (losses t) (iterateVariable interval rates losses 0 t)‖ ^ 2) -
      ‖iterateVariable interval rates losses 0 2 - 0‖ ^ 2 / (2 * rates (2 - 1)) := by
  apply theorem_2_13_variable interval (by exact isCompact_Icc.isBounded)
    rates losses 0 (by norm_num [interval]) 2 (by decide)
  · intro t ht
    simp only [rates]
    split_ifs <;> norm_num
  · intro t ht
    have : t = 0 := by omega
    subst t
    norm_num [rates]
  · exact fun t ht => losses_regular t
  · norm_num [interval]

/-- A zero potential and single round exercise the allowed zero diameter/positive horizon boundary. -/
example : (∑ t ∈ range 1, ((0 : ℝ) - 0) / (2 * rates t)) ≤
    0 / (2 * rates (1 - 1)) - 0 / (2 * rates (1 - 1)) :=
  weighted_potential_sum (fun _ => 0) rates 0 1 (by decide)
    (by
      intro t ht
      have : t = 0 := by omega
      subst t
      norm_num [rates])
    (by intro t ht; omega) (by intro t ht; rfl)

#print axioms BanditRL.OnlineGradientDescent.iterateVariable_mem
#print axioms BanditRL.OnlineGradientDescent.iterateVariable_prefix
#print axioms BanditRL.OnlineGradientDescent.variable_one_step
#print axioms BanditRL.OnlineGradientDescent.weighted_potential_sum
#print axioms BanditRL.OnlineGradientDescent.theorem_2_13_variable_bound
#print axioms BanditRL.OnlineGradientDescent.theorem_2_13_variable
#print axioms nondegenerate

end Tests.OnlineGradientDescentVariable
