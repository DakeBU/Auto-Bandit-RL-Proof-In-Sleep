import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
#check (∀ (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ),
    energy V α D loss x₁ p t ≤ energy V α D loss x₁ p (t + 1))

#check (∀ (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hg : selected V α D loss x₁ p t ≠ 0),
    0 < energy V α D loss x₁ p (t + 1))

#check (∀ (V : Domain (E := E)) (α D : ℝ) (hα : 0 < α) (hD : 0 < D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hg : selected V α D loss x₁ p t ≠ 0),
    0 < eta V α D loss x₁ p t)

#check (∀ (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V α D loss x₁ p t ∈ SourceSubdifferential (loss t) (output V α D loss x₁ p t))
    (hz : selected V α D loss x₁ p t = 0) (u : E) (hu : u ∈ V.carrier),
    output V α D loss x₁ p (t + 1) = output V α D loss x₁ p t ∧
    (loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal ≤ 0)

#check (∀ (V : Domain (E := E)) (α D : ℝ) (hα : 0 < α) (hD : 0 < D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V α D loss x₁ p t ∈ SourceSubdifferential (loss t) (output V α D loss x₁ p t))
    (hnz : selected V α D loss x₁ p t ≠ 0) (u : E) (hu : u ∈ V.carrier),
    eta V α D loss x₁ p t * ((loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal) ≤
      eta V α D loss x₁ p t * inner ℝ (selected V α D loss x₁ p t) (output V α D loss x₁ p t - u) ∧
    eta V α D loss x₁ p t * inner ℝ (selected V α D loss x₁ p t) (output V α D loss x₁ p t - u) ≤
      ‖output V α D loss x₁ p t - u‖ ^ 2 / 2 -
      ‖output V α D loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
      (eta V α D loss x₁ p t) ^ 2 / 2 * ‖selected V α D loss x₁ p t‖ ^ 2)

#check (∀ (V : Domain (E := E)) (α D : ℝ) (hα : 0 < α) (hD : 0 < D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V α D loss x₁ p t ∈ SourceSubdifferential (loss t) (output V α D loss x₁ p t)) (u : E) (hu : u ∈ V.carrier),
    (loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal ≤
      (‖output V α D loss x₁ p t - u‖ ^ 2 - ‖output V α D loss x₁ p (t + 1) - u‖ ^ 2) *
        Real.sqrt (energy V α D loss x₁ p (t + 1)) / (2 * α * D) +
      α * D / 2 * (‖selected V α D loss x₁ p t‖ ^ 2 / Real.sqrt (energy V α D loss x₁ p (t + 1))))

#check (∀ (V : Domain (E := E)) (α : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ (0 : ℝ))
    (u : E) (hu : u ∈ V.carrier),
    regret V α 0 loss x₁ p u T = 0 ∧ ‖output V α 0 loss x₁ p T - u‖ = 0)

end BanditRL.OnlineAdaptiveOSD
