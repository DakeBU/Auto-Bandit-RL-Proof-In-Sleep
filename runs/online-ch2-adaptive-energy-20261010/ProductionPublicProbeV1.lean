import BanditRLProof.OnlineAdaptiveEnergy

open Finset

#check BanditRL.OnlineAdaptiveEnergy.sum_div_sqrt_prefix
example : ∀ (a : ℕ → ℝ) (T : ℕ), (∀ t < T, 0 ≤ a t) →
    (∑ t ∈ range T, a t / Real.sqrt (∑ i ∈ range (t + 1), a i)) ≤
      2 * Real.sqrt (∑ i ∈ range T, a i) :=
  BanditRL.OnlineAdaptiveEnergy.sum_div_sqrt_prefix

#check BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix
example {E : Type*} [NormedAddCommGroup E] : ∀ (g : ℕ → E) (T : ℕ),
    (∑ t ∈ range T, ‖g t‖ ^ 2 / Real.sqrt (∑ i ∈ range (t + 1), ‖g i‖ ^ 2)) ≤
      2 * Real.sqrt (∑ i ∈ range T, ‖g i‖ ^ 2) :=
  BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix

#check BanditRL.OnlineAdaptiveEnergy.source_energy_term_bound
example {E : Type*} [NormedAddCommGroup E] : ∀ (g : ℕ → E) (T : ℕ) (D : ℝ), 0 ≤ D →
    D / 2 * (∑ t ∈ range T,
      ‖g t‖ ^ 2 / Real.sqrt (∑ i ∈ range (t + 1), ‖g i‖ ^ 2)) ≤
      D * Real.sqrt (∑ i ∈ range T, ‖g i‖ ^ 2) :=
  BanditRL.OnlineAdaptiveEnergy.source_energy_term_bound

#print axioms BanditRL.OnlineAdaptiveEnergy.sum_div_sqrt_prefix
#print axioms BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix
#print axioms BanditRL.OnlineAdaptiveEnergy.source_energy_term_bound
#print BanditRL.OnlineAdaptiveEnergy.sum_div_sqrt_prefix
#print BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix
#print BanditRL.OnlineAdaptiveEnergy.source_energy_term_bound
