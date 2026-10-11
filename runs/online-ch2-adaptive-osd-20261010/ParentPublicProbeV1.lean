import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E

example (V : Domain (E := E)) (α D : ℝ) (hα : 0 < α) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V α D loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :
    regret V α D loss x₁ p u T ≤
      (1 / (2 * α) + α) * D * Real.sqrt (energy V α D loss x₁ p T) -
      ‖output V α D loss x₁ p T - u‖ ^ 2 * Real.sqrt (energy V α D loss x₁ p T) / (2 * α * D) := by
  exact BanditRL.OnlineAdaptiveOSD.regret_bound V α D hα hD loss x₁ p hx₁ T hloss hlegal hdiam u hu
#check BanditRL.OnlineAdaptiveOSD.regret_bound
#print axioms BanditRL.OnlineAdaptiveOSD.regret_bound
end BanditRL.OnlineAdaptiveOSD
