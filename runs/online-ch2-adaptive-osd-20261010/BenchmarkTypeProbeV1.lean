import BanditRLProof.OnlineOptimalStep
import BanditRLProof.OnlineAdaptiveOSD

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineAdaptiveOSD
namespace BanditRL.OnlineAdaptiveBenchmark
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
#check (∀ (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S),
    IsGLB {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η} (D * Real.sqrt S))
#check (∀ (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S),
    D * Real.sqrt (2 * S) = Real.sqrt 2 * sInf
      {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η})
#check (∀ (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S),
    (∃ η : ℝ, 0 < η ∧ BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η = D * Real.sqrt S) ↔
      (0 < D ∧ 0 < S) ∨ (D = 0 ∧ S = 0))
#check (∀ (D S : ℝ) (hD : 0 < D) (hS : 0 < S),
    0 < D / Real.sqrt S ∧
    BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S (D / Real.sqrt S) = D * Real.sqrt S ∧
    ∀ η : ℝ, 0 < η →
      D * Real.sqrt S ≤ BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η ∧
      (BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η = D * Real.sqrt S ↔
        η = D / Real.sqrt S))
#check (∀ (V : Domain (E := E)) (D : ℝ) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hconvex : ∀ t < T, IsConvexExtended (loss t))
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (Real.sqrt 2 / 2) D loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier),
    regret V (Real.sqrt 2 / 2) D loss x₁ p u T ≤
      D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ p T) ∧
    D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ p T) =
      Real.sqrt 2 * sInf {b : ℝ | ∃ η : ℝ, 0 < η ∧
        b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2)
          (energy V (Real.sqrt 2 / 2) D loss x₁ p T) η})
#check BanditRL.OnlineOptimalStep.lower_bound
#check BanditRL.OnlineOptimalStep.distance_energy_argmin
#check BanditRL.OnlineOptimalStep.optimal_unique
#check BanditRL.OnlineOptimalStep.zero_distance_decreases
#check BanditRL.OnlineOptimalStep.zero_energy_decreases
#check IsGLB.csInf_eq
end BanditRL.OnlineAdaptiveBenchmark
