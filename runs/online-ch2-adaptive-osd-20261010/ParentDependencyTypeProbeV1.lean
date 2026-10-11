import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
#check BanditRL.OnlineAdaptivePotential.weighted_potential_sum
#check BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix
#check BanditRL.OnlineAdaptiveOSD.one_step
#check BanditRL.OnlineAdaptiveOSD.energy_eq_sum
#check BanditRL.OnlineAdaptiveOSD.energy_step_mono
#check BanditRL.OnlineAdaptiveOSD.output_mem
#check BanditRL.OnlineAdaptiveOSD.regret_zero_diameter
#check (∀ (V : Domain (E := E)) (α D : ℝ) (hα : 0 < α) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V α D loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier),
    regret V α D loss x₁ p u T ≤
      (1 / (2 * α) + α) * D * Real.sqrt (energy V α D loss x₁ p T) -
      ‖output V α D loss x₁ p T - u‖ ^ 2 * Real.sqrt (energy V α D loss x₁ p T) / (2 * α * D))
end BanditRL.OnlineAdaptiveOSD
