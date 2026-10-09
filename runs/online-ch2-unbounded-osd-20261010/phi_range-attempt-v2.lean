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
    simpa only [Pi.sub_apply, id_eq, zero_sub, sub_self, Real.rpow_zero, mul_one, mul_neg_one] using
      (((hasDerivAt_const (1 : ℝ) 1).sub (hasDerivAt_id 1)).const_rpow
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hs := hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)
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

namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem switching_loss_regular (T : ℕ) (v : E) (hv : ‖v‖ = 1) (t : ℕ) :
    ConvexOn ℝ univ (switchLoss T v t) ∧ LipschitzWith 1 (switchLoss T v t) := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [switchLoss]
    simp only [inner_add_right, inner_smul_right, smul_eq_mul]
    exact le_of_eq (by ring)
  · apply LipschitzWith.mk_one
    intro x y
    have hs : |switchSlope T t| = 1 := by
      unfold switchSlope
      split <;> norm_num
    calc
      dist (switchLoss T v t x) (switchLoss T v t y) =
          |switchSlope T t| * |inner ℝ v (x - y)| := by
        rw [Real.dist_eq]
        change |switchSlope T t * inner ℝ v x - switchSlope T t * inner ℝ v y| = _
        rw [← mul_sub, ← inner_sub_right, abs_mul]
      _ ≤ 1 * (‖v‖ * ‖x - y‖) := by
        rw [hs]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v (x - y)) zero_le_one
      _ = dist x y := by rw [hv, one_mul, one_mul, dist_eq_norm]

end BanditRL.OnlineUnboundedOSD

namespace BanditRL.OnlineUnboundedOSD

theorem phi_range (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    0 < phi α ∧ phi α < 1 - Real.log 2 := by
  let β : ℝ := 1 - α
  have hb0 : 0 < β := by dsimp [β]; linarith
  have hb1 : β < 1 := by dsimp [β]; linarith
  have hbp : 0 < 1 + β := by linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  let q : ℝ → ℝ := fun z => (1 + z) * (1 / 2 : ℝ) ^ z
  let dq : ℝ → ℝ := fun z => (1 - (1 + z) * Real.log 2) * (1 / 2 : ℝ) ^ z
  let ddq : ℝ → ℝ := fun z =>
    Real.log 2 * ((1 + z) * Real.log 2 - 2) * (1 / 2 : ℝ) ^ z
  have hd (z : ℝ) : HasDerivAt q (dq z) z := by
    have h := ((hasDerivAt_const z 1).add (hasDerivAt_id z)).mul
      ((hasDerivAt_id z).const_rpow (by norm_num : (0 : ℝ) < 1 / 2))
    convert h using 1 <;> dsimp [q, dq] <;> simp only [hlog] <;> ring
  have hdd (z : ℝ) : HasDerivAt dq (ddq z) z := by
    have h := ((hasDerivAt_const z 1).sub
      (((hasDerivAt_const z 1).add (hasDerivAt_id z)).mul_const (Real.log 2))).mul
      ((hasDerivAt_id z).const_rpow (by norm_num : (0 : ℝ) < 1 / 2))
    convert h using 1 <;> dsimp [dq, ddq] <;> simp only [hlog] <;> ring
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) q := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
      (fun z hz => (hd z).continuousAt.continuousWithinAt)
      (fun z hz => (hd z).hasDerivWithinAt)
      (fun z hz => (hdd z).hasDerivWithinAt)
    intro z hz
    have hz1 : z ≤ 1 := (interior_subset hz).2
    have hneg : (1 + z) * Real.log 2 - 2 ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hl0.le hneg)
      (Real.rpow_nonneg (by norm_num) z)
  have hbern : (2 : ℝ) ^ β < 1 + β := by
    simpa using rpow_one_add_lt_one_add_mul_self
      (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≠ 0) hb0 hb1
  have hp : 0 < (1 / 2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  have hprod : (2 : ℝ) ^ β * (1 / 2 : ℝ) ^ β = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hq : 1 < q β := by
    have hm := mul_lt_mul_of_pos_right hbern hp
    dsimp [q]
    rwa [hprod] at hm
  have hphi : phi α = (q β - 1) / (β * (1 + β)) := by
    dsimp [phi, q]
    rw [show 1 - α = β by rfl, show 2 - α = 1 + β by dsimp [β]; ring]
    field_simp
    <;> ring
  have hs : (q β - 1) / β ≤ 1 - Real.log 2 := by
    simpa [slope_def_field, q, dq] using
      hconc.slope_le_of_hasDerivAt (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
        (show β ∈ Set.Icc 0 1 from ⟨hb0.le, hb1.le⟩) hb0 (hd 0)
  constructor
  · rw [hphi]
    exact div_pos (sub_pos.mpr hq) (mul_pos hb0 hbp)
  · rw [hphi, div_lt_iff₀ (mul_pos hb0 hbp)]
    have hnum := (div_le_iff₀ hb0).mp hs
    have hc : 0 < (1 - Real.log 2) * β := mul_pos (sub_pos.mpr hl1) hb0
    nlinarith

end BanditRL.OnlineUnboundedOSD
