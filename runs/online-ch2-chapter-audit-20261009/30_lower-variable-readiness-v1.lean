import Tests.OnlineGradientDescentSourceCanary

noncomputable section
open Set Finset BanditRL.OnlineGradientDescent
open BanditRL.OnlineGradientDescentSource
open scoped InnerProductSpace
namespace Chapter2CurrentReadiness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

example (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (D : ℝ) (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) : regretVariable V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) - ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  exact BanditRL.OnlineGradientDescentSource.theorem_2_13_variable_bound V η loss x₁ hx₁ T hT hη hmono hloss D hdiam u hu

example (V : Domain E) (hV : Bornology.IsBounded V.carrier) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) : regretVariable V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) - ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  exact BanditRL.OnlineGradientDescentSource.theorem_2_13_variable V hV η loss x₁ hx₁ T hT hη hmono hloss u hu

-- Whole public values below are scratch witnesses, not new production declarations.
noncomputable def prefixValue := @BanditRL.OnlineGradientDescent.iterateVariable_prefix
noncomputable def feasibilityValue := @BanditRL.OnlineGradientDescent.iterateVariable_mem
noncomputable def sourceAdapterValue := @BanditRL.OnlineGradientDescentSource.source_to_feasible
noncomputable def concreteVariableValue := @Tests.OnlineGradientDescentSource.active_projection_variable
noncomputable def concreteNondegenerateValue := @Tests.OnlineGradientDescentVariable.nondegenerate

#check @BanditRL.OnlineGradientDescentSource.theorem_2_13_variable_bound
#check @BanditRL.OnlineGradientDescentSource.theorem_2_13_variable
#check @Tests.OnlineGradientDescentSource.active_projection_variable
#print axioms BanditRL.OnlineGradientDescentSource.theorem_2_13_variable_bound
#print axioms BanditRL.OnlineGradientDescentSource.theorem_2_13_variable
#print axioms prefixValue
#print axioms feasibilityValue
#print axioms sourceAdapterValue
#print axioms concreteVariableValue
#print axioms concreteNondegenerateValue
end Chapter2CurrentReadiness
