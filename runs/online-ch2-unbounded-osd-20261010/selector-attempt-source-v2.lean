import BanditRLProof.OnlineSubgradientDescent
import BanditRLProof.OnlineHinge
import BanditRLProof.OnlineHuber
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
noncomputable section
open Set Finset Filter Topology
open scoped InnerProductSpace
set_option autoImplicit false
namespace BanditRL.OnlineUnboundedOSD
def powerSteps (α : ℝ) (t : ℕ) : ℝ := ((t + 1 : ℕ) : ℝ) ^ (-α)
def phi (α : ℝ) : ℝ := 1 / (2 - α) + ((1 / 2 : ℝ) ^ (1 - α) - 1) / (1 - α)
def switchSlope (T t : ℕ) : ℝ := if t < (T + 1) / 2 then -1 else 1
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def switchLoss (T : ℕ) (v : E) (t : ℕ) (z : E) : ℝ := switchSlope T t * inner ℝ v z
end BanditRL.OnlineUnboundedOSD

/-!
Required Chapter2 unbounded varying-step OSD failure dependency, Orabona v10
Theorem5.4 printed52-53/PDF64-65. Four source witness definitions and eleven
terminal contracts are frozen before lowering. This actual selector producer is
only the first dependency-ready leaf; the complete lower bound/phi range/limit,
canaries, combined project and publication gates remain open. No chapter closure.
-/
namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem currentSubgradient_affine (a x : E) (b : ℝ) :
    BanditRL.OnlineSubgradientDescent.currentSubgradient
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x = a := by
  classical
  have hs : (BanditRL.OnlineConvex.SourceSubdifferential
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x).Nonempty := by
    rw [BanditRL.OnlineConvex.affine_subdifferential a b x]
    exact Set.singleton_nonempty a
  unfold BanditRL.OnlineSubgradientDescent.currentSubgradient
  rw [dif_pos hs]
  have hc := Classical.choose_spec hs
  have hsub : BanditRL.OnlineConvex.SourceSubdifferential
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x ⊆ {a} := by
    intro z hz
    rwa [BanditRL.OnlineConvex.affine_subdifferential a b x] at hz
  exact Set.mem_singleton_iff.mp (hsub hc)

end BanditRL.OnlineUnboundedOSD
