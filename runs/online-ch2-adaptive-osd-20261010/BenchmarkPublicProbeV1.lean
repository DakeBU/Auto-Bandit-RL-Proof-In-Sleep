import BanditRLProof.OnlineOptimalStep
import BanditRLProof.OnlineAdaptiveOSD

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineAdaptiveOSD
namespace BanditRL.OnlineAdaptiveBenchmark
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

example (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S) :
    IsGLB {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η} (D * Real.sqrt S) := by
  exact BanditRL.OnlineAdaptiveBenchmark.benchmark_isGLB D S hD hS
#check BanditRL.OnlineAdaptiveBenchmark.benchmark_isGLB
#print axioms BanditRL.OnlineAdaptiveBenchmark.benchmark_isGLB

example (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S) :
    D * Real.sqrt (2 * S) = Real.sqrt 2 * sInf
      {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η} := by
  exact BanditRL.OnlineAdaptiveBenchmark.source_benchmark_value D S hD hS
#check BanditRL.OnlineAdaptiveBenchmark.source_benchmark_value
#print axioms BanditRL.OnlineAdaptiveBenchmark.source_benchmark_value

example (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S) :
    (∃ η : ℝ, 0 < η ∧ BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η = D * Real.sqrt S) ↔
      (0 < D ∧ 0 < S) ∨ (D = 0 ∧ S = 0) := by
  exact BanditRL.OnlineAdaptiveBenchmark.benchmark_attained_iff D S hD hS
#check BanditRL.OnlineAdaptiveBenchmark.benchmark_attained_iff
#print axioms BanditRL.OnlineAdaptiveBenchmark.benchmark_attained_iff

example (D S : ℝ) (hD : 0 < D) (hS : 0 < S) :
    0 < D / Real.sqrt S ∧
    BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S (D / Real.sqrt S) = D * Real.sqrt S ∧
    ∀ η : ℝ, 0 < η →
      D * Real.sqrt S ≤ BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η ∧
      (BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η = D * Real.sqrt S ↔
        η = D / Real.sqrt S) := by
  exact BanditRL.OnlineAdaptiveBenchmark.benchmark_positive_minimum D S hD hS
#check BanditRL.OnlineAdaptiveBenchmark.benchmark_positive_minimum
#print axioms BanditRL.OnlineAdaptiveBenchmark.benchmark_positive_minimum

example (V : Domain (E := E)) (D : ℝ) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hconvex : ∀ t < T, IsConvexExtended (loss t))
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (Real.sqrt 2 / 2) D loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :
    regret V (Real.sqrt 2 / 2) D loss x₁ p u T ≤
      D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ p T) ∧
    D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ p T) =
      Real.sqrt 2 * sInf {b : ℝ | ∃ η : ℝ, 0 < η ∧
        b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2)
          (energy V (Real.sqrt 2 / 2) D loss x₁ p T) η} := by
  exact BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum V D hD loss x₁ p hx₁ T hconvex hloss hlegal hdiam u hu
#check BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum
#print axioms BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum

end BanditRL.OnlineAdaptiveBenchmark
