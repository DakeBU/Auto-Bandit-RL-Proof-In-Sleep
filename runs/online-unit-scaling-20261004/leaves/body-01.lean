import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineHuber
import BanditRLProof.OnlineAffineSubgradient
import BanditRLProof.OnlineOptimalStep
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineSubgradientPolicy
open scoped InnerProductSpace
namespace BanditRL.OnlineUnitScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

abbrev V : Domain (E := E) := BanditRL.OnlineHuber.fullSpace
def scaledLoss (c : ℝ) (f : E → EReal) : E → EReal := fun y => f (c • y)
def scaledEta (c : ℝ) (η : ℕ → ℝ) : ℕ → ℝ := fun t => η t / c ^ 2
def scaledPolicy (c : ℝ) (p : SupportPolicy (E := E)) : SupportPolicy (E := E) :=
  fun t past h f => c • p t (fun i => scaledLoss c⁻¹ (past i))
    (fun i => c • h i) (scaledLoss c⁻¹ f)

theorem unit_exponents {D : Type*} [AddCommGroup D] (X L H : D) (h : H + (L - X) = X) :
    H = X + X - L := by
  calc
    H = (H + (L - X)) - (L - X) := by abel
    _ = X - (L - X) := by rw [h]
    _ = X + X - L := by abel

theorem regret_unit_exponents {D : Type*} [AddCommGroup D] (X L : D) :
    (X + X - (X + X - L) = L) ∧ ((X + X - L) + (L - X) + (L - X) = L) := by
  constructor <;> abel

end BanditRL.OnlineUnitScaling
