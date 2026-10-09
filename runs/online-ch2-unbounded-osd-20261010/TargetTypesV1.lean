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
namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
#check fun (a x : E) (b : ℝ) =>
  (BanditRL.OnlineSubgradientDescent.currentSubgradient
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x = a : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
#check fun (η : ℝ) (a x : E) (b : ℝ) =>
  (BanditRL.OnlineSubgradientDescent.step BanditRL.OnlineHuber.fullSpace η
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x = x - η • a : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
#check fun (η : ℕ → ℝ) (a : ℕ → E) (b : ℕ → ℝ)
    (x0 : E) (t : ℕ) =>
  (BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace η
      (fun s z => ((inner ℝ (a s) z + b s : ℝ) : EReal)) x0 t =
      x0 - ∑ s ∈ range t, η s • a s : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
#check fun (α : ℝ) (t : ℕ) =>
  (0 < powerSteps α t : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
#check fun (T : ℕ) (v : E) (hv : ‖v‖ = 1) (t : ℕ) =>
  (ConvexOn ℝ univ (switchLoss T v t) ∧ LipschitzWith 1 (switchLoss T v t) : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
#check fun (α : ℝ) (T : ℕ) =>
  (BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
      (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T =
      -((((T + 1) / 2 : ℕ) : ℝ) - ((T / 2 : ℕ) : ℝ)) *
        (∑ i ∈ range ((T + 1) / 2), powerSteps α i) +
      (∑ i ∈ range T, ((i + 1 : ℕ) : ℝ) ^ (1 - α)) -
      (T : ℝ) * (∑ i ∈ Ico ((T + 1) / 2) T, powerSteps α i) : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
#check fun (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) =>
  (0 < phi α ∧ phi α < 1 - Real.log 2 : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
#check fun  =>
  (Tendsto phi (𝓝[<] (1 : ℝ)) (𝓝 (1 - Real.log 2)) ∧
      (3 / 10 : ℝ) ≤ 1 - Real.log 2 : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
#check fun (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) =>
  ((1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
      (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
#check fun (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) (v : E) (hv : ‖v‖ = 1) =>
  ((1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T v t z : EReal)) 0 0 T : Prop)
end BanditRL.OnlineUnboundedOSD
namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
#check fun [Nontrivial E] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) =>
  (∃ loss : ℕ → E → ℝ,
      (∀ t < T, ConvexOn ℝ univ (loss t) ∧ LipschitzWith 1 (loss t)) ∧
      (1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
        BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
          (fun t z => (loss t z : EReal)) 0 0 T : Prop)
end BanditRL.OnlineUnboundedOSD
