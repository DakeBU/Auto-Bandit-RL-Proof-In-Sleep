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

namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem step_affine_fullSpace (η : ℝ) (a x : E) (b : ℝ) :
    BanditRL.OnlineSubgradientDescent.step BanditRL.OnlineHuber.fullSpace η
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x = x - η • a := by
  unfold BanditRL.OnlineSubgradientDescent.step
  rw [currentSubgradient_affine, BanditRL.OnlineHuber.project_fullSpace]

end BanditRL.OnlineUnboundedOSD

namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem iterate_affine_prefix (η : ℕ → ℝ) (a : ℕ → E) (b : ℕ → ℝ)
    (x0 : E) (t : ℕ) :
    BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace η
      (fun s z => ((inner ℝ (a s) z + b s : ℝ) : EReal)) x0 t =
      x0 - ∑ s ∈ range t, η s • a s := by
  induction t with
  | zero => simp [BanditRL.OnlineSubgradientDescent.iterate]
  | succ t ih =>
      rw [BanditRL.OnlineSubgradientDescent.iterate, step_affine_fullSpace, ih,
        Finset.sum_range_succ]
      abel

end BanditRL.OnlineUnboundedOSD

namespace BanditRL.OnlineUnboundedOSD

theorem powerSteps_pos (α : ℝ) (t : ℕ) :
    0 < powerSteps α t := by
  unfold powerSteps
  exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos t) (-α)

end BanditRL.OnlineUnboundedOSD

namespace BanditRL.OnlineUnboundedOSD

theorem phi_limit :
    Tendsto phi (𝓝[<] (1 : ℝ)) (𝓝 (1 - Real.log 2)) ∧
      (3 / 10 : ℝ) ≤ 1 - Real.log 2 := by
  have hd : HasDerivAt (fun z : ℝ => (1 / 2 : ℝ) ^ (1 - z))
      (-Real.log (1 / 2 : ℝ)) 1 := by
    simpa only [zero_sub, sub_self, Real.rpow_zero, mul_one, mul_neg_one] using
      (((hasDerivAt_const (1 : ℝ) 1).sub (hasDerivAt_id 1)).const_rpow
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hs := hd.tendsto_slope.mono_left nhdsLT_le_nhdsNE
  have heq : (fun z : ℝ => ((1 / 2 : ℝ) ^ (1 - z) - 1) / (1 - z)) =
      (fun z => -slope (fun y : ℝ => (1 / 2 : ℝ) ^ (1 - y)) 1 z) := by
    funext z
    simp only [slope_def_field, sub_self, Real.rpow_zero]
    rw [show 1 - z = -(z - 1) by ring, div_neg]
  have hsecond : Tendsto (fun z : ℝ => ((1 / 2 : ℝ) ^ (1 - z) - 1) / (1 - z))
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log (1 / 2 : ℝ))) := by
    rw [heq]
    simpa only [neg_neg] using hs.neg
  have hc : ContinuousAt (fun z : ℝ => 1 / (2 - z)) 1 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hfirst : Tendsto (fun z : ℝ => 1 / (2 - z)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  constructor
  · have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    simpa only [phi, hlog, sub_eq_add_neg] using hfirst.add hsecond
  · linarith [Real.log_two_lt_d9]

end BanditRL.OnlineUnboundedOSD
