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

#check hasGradientAt_iff_hasFDerivAt
#check HasGradientAt.hasFDerivAt
#check HasFDerivAt.comp
#check ContinuousLinearMap.hasFDerivAt
#check map_smulₛₗ
#check ContinuousLinearMap.adjoint_id
#check BanditRL.OnlineConvex.theorem_2_28
#check inv_smul_smul₀
#check smul_inv_smul₀
#check real_inner_smul_left
#check real_inner_smul_right
#check norm_smul
#check Fin.lastCases
#check BanditRL.OnlineSubgradientPolicy.regret_fixed
#check BanditRL.OnlineHuber.project_fullSpace
end BanditRL.OnlineUnitScaling
