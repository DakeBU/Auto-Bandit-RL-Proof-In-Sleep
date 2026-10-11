import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E

example (V : Domain (E := E)) (D : ℝ) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hconvex : ∀ t < T, IsConvexExtended (loss t))
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V 1 D loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :
    regret V 1 D loss x₁ p u T ≤
      (3 / 2 : ℝ) * D * Real.sqrt (energy V 1 D loss x₁ p T) := by
  exact BanditRL.OnlineAdaptiveOSD.source_eq4_4 V D hD loss x₁ p hx₁ T hconvex hloss hlegal hdiam u hu
#check BanditRL.OnlineAdaptiveOSD.source_eq4_4
#print axioms BanditRL.OnlineAdaptiveOSD.source_eq4_4

example (V : Domain (E := E)) (D : ℝ) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hconvex : ∀ t < T, IsConvexExtended (loss t))
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :
    regret V 1 D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy u T ≤
      (3 / 2 : ℝ) * D * Real.sqrt (energy V 1 D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy T) := by
  exact BanditRL.OnlineAdaptiveOSD.canonical_eq4_4 V D hD loss x₁ hx₁ T hconvex hloss hdiam u hu
#check BanditRL.OnlineAdaptiveOSD.canonical_eq4_4
#print axioms BanditRL.OnlineAdaptiveOSD.canonical_eq4_4

example (V : Domain (E := E)) (D : ℝ) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hconvex : ∀ t < T, IsConvexExtended (loss t))
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (Real.sqrt 2 / 2) D loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :
    regret V (Real.sqrt 2 / 2) D loss x₁ p u T ≤
      D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ p T) := by
  exact BanditRL.OnlineAdaptiveOSD.source_theorem4_14 V D hD loss x₁ p hx₁ T hconvex hloss hlegal hdiam u hu
#check BanditRL.OnlineAdaptiveOSD.source_theorem4_14
#print axioms BanditRL.OnlineAdaptiveOSD.source_theorem4_14

example (V : Domain (E := E)) (D : ℝ) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hconvex : ∀ t < T, IsConvexExtended (loss t))
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :
    regret V (Real.sqrt 2 / 2) D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy u T ≤
      D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy T) := by
  exact BanditRL.OnlineAdaptiveOSD.canonical_theorem4_14 V D hD loss x₁ hx₁ T hconvex hloss hdiam u hu
#check BanditRL.OnlineAdaptiveOSD.canonical_theorem4_14
#print axioms BanditRL.OnlineAdaptiveOSD.canonical_theorem4_14

end BanditRL.OnlineAdaptiveOSD
