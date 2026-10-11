import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E

example (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    state V α D loss x₁ p (t + 1) =
      (Fin.snoc (history V α D loss x₁ p t)
        (if selected V α D loss x₁ p t = 0 then output V α D loss x₁ p t else
          BanditRL.OnlineGradientDescent.project V
            (output V α D loss x₁ p t - eta V α D loss x₁ p t • selected V α D loss x₁ p t)),
       energy V α D loss x₁ p t + ‖selected V α D loss x₁ p t‖ ^ 2) := by
  exact BanditRL.OnlineAdaptiveOSD.state_succ V α D loss x₁ p t
#check BanditRL.OnlineAdaptiveOSD.state_succ
#print axioms BanditRL.OnlineAdaptiveOSD.state_succ

example (V : Domain (E := E)) (α D : ℝ) (loss loss' : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hloss : ∀ s < t, loss s = loss' s) :
    state V α D loss x₁ p t = state V α D loss' x₁ p t := by
  exact BanditRL.OnlineAdaptiveOSD.state_prefix V α D loss loss' x₁ p t hloss
#check BanditRL.OnlineAdaptiveOSD.state_prefix
#print axioms BanditRL.OnlineAdaptiveOSD.state_prefix

end BanditRL.OnlineAdaptiveOSD
