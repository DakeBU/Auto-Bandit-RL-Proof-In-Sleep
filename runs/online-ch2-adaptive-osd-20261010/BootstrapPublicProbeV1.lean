import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    energy V α D loss x₁ p (t + 1) =
      energy V α D loss x₁ p t + ‖selected V α D loss x₁ p t‖ ^ 2 := by
  exact BanditRL.OnlineAdaptiveOSD.energy_succ V α D loss x₁ p t
#check BanditRL.OnlineAdaptiveOSD.energy_succ
#print axioms BanditRL.OnlineAdaptiveOSD.energy_succ

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    output V α D loss x₁ p (t + 1) =
      if selected V α D loss x₁ p t = 0 then output V α D loss x₁ p t else
        BanditRL.OnlineGradientDescent.project V
          (output V α D loss x₁ p t - eta V α D loss x₁ p t • selected V α D loss x₁ p t) := by
  exact BanditRL.OnlineAdaptiveOSD.output_succ V α D loss x₁ p t
#check BanditRL.OnlineAdaptiveOSD.output_succ
#print axioms BanditRL.OnlineAdaptiveOSD.output_succ

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) :
    energy V α D loss x₁ p T = ∑ t ∈ range T, ‖selected V α D loss x₁ p t‖ ^ 2 := by
  exact BanditRL.OnlineAdaptiveOSD.energy_eq_sum V α D loss x₁ p T
#check BanditRL.OnlineAdaptiveOSD.energy_eq_sum
#print axioms BanditRL.OnlineAdaptiveOSD.energy_eq_sum

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (i : Fin (t + 1)) :
    history V α D loss x₁ p t i ∈ V.carrier := by
  exact BanditRL.OnlineAdaptiveOSD.history_mem V α D loss x₁ p hx₁ t i
#check BanditRL.OnlineAdaptiveOSD.history_mem
#print axioms BanditRL.OnlineAdaptiveOSD.history_mem

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) :
    output V α D loss x₁ p t ∈ V.carrier := by
  exact BanditRL.OnlineAdaptiveOSD.output_mem V α D loss x₁ p hx₁ t
#check BanditRL.OnlineAdaptiveOSD.output_mem
#print axioms BanditRL.OnlineAdaptiveOSD.output_mem

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) :
    0 ≤ energy V α D loss x₁ p T := by
  exact BanditRL.OnlineAdaptiveOSD.energy_nonneg V α D loss x₁ p T
#check BanditRL.OnlineAdaptiveOSD.energy_nonneg
#print axioms BanditRL.OnlineAdaptiveOSD.energy_nonneg

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    eta V α D loss x₁ p t = α * D / Real.sqrt (energy V α D loss x₁ p (t + 1)) := by
  exact BanditRL.OnlineAdaptiveOSD.eta_eq_energy V α D loss x₁ p t
#check BanditRL.OnlineAdaptiveOSD.eta_eq_energy
#print axioms BanditRL.OnlineAdaptiveOSD.eta_eq_energy

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier) :
    loss t (output V α D loss x₁ p t) = ((loss t (output V α D loss x₁ p t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal) := by
  exact BanditRL.OnlineAdaptiveOSD.trajectory_finite_loss V α D loss x₁ p hx₁ t hloss u hu
#check BanditRL.OnlineAdaptiveOSD.trajectory_finite_loss
#print axioms BanditRL.OnlineAdaptiveOSD.trajectory_finite_loss

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hp : BanditRL.OnlineSubgradientPolicy.OracleLaw V p)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback V α D loss x₁ p T := by
  exact BanditRL.OnlineAdaptiveOSD.oracle_feedback V α D loss x₁ p hx₁ T hp hloss
#check BanditRL.OnlineAdaptiveOSD.oracle_feedback
#print axioms BanditRL.OnlineAdaptiveOSD.oracle_feedback

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback V α D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy T := by
  exact BanditRL.OnlineAdaptiveOSD.canonical_feedback V α D loss x₁ hx₁ T hloss
#check BanditRL.OnlineAdaptiveOSD.canonical_feedback
#print axioms BanditRL.OnlineAdaptiveOSD.canonical_feedback

end BanditRL.OnlineAdaptiveOSD
