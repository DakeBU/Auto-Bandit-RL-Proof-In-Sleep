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
    convert rpow_one_add_lt_one_add_mul_self
      (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≠ 0) hb0 hb1 using 1 <;> norm_num
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

namespace BanditRL.OnlineUnboundedOSD

theorem switching_scalar_regret_identity (α : ℝ) (T : ℕ) :
    BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
      (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T =
      -((((T + 1) / 2 : ℕ) : ℝ) - ((T / 2 : ℕ) : ℝ)) *
        (∑ i ∈ range ((T + 1) / 2), powerSteps α i) +
      (∑ i ∈ range T, ((i + 1 : ℕ) : ℝ) ^ (1 - α)) -
      (T : ℝ) * (∑ i ∈ Ico ((T + 1) / 2) T, powerSteps α i) := by
  classical
  have hin (a b : ℝ) : inner ℝ a b = b * a := rfl
  let m : ℕ := (T + 1) / 2
  let k : ℕ := T / 2
  have hmT : m ≤ T := by dsimp [m]; omega
  have hmk : m + k = T := by dsimp [m, k]; omega
  have hcast : (T : ℝ) = (m : ℝ) + (k : ℝ) := by exact_mod_cast hmk.symm
  have hc (n : ℕ) : (∑ t ∈ range n, switchSlope T t) =
      (n : ℝ) - 2 * ((min n m : ℕ) : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      by_cases hn : n < m
      · rw [show switchSlope T n = -1 by change (if n < m then (-1 : ℝ) else 1) = -1; exact if_pos hn,
          min_eq_left (Nat.le_of_lt hn), min_eq_left (Nat.succ_le_of_lt hn)]
        push_cast
        ring
      · have hmn : m ≤ n := Nat.le_of_not_gt hn
        rw [show switchSlope T n = 1 by change (if n < m then (-1 : ℝ) else 1) = 1; exact if_neg hn,
          min_eq_right hmn, min_eq_right (hmn.trans (Nat.le_succ n))]
        push_cast
        ring
  have hsuf (i : ℕ) (hi : i < T) : (∑ t ∈ Ico (i + 1) T, switchSlope T t) =
      (T : ℝ) - 2 * (m : ℝ) - (((i + 1 : ℕ) : ℝ) - 2 * ((min (i + 1) m : ℕ) : ℝ)) := by
    rw [sum_Ico_eq_sub _ (Nat.succ_le_of_lt hi), hc T, hc (i + 1), min_eq_right hmT]
  have hrun (t : ℕ) :
      BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 t =
      -(∑ i ∈ range t, powerSteps α i * switchSlope T i) := by
    have hloss : (fun (s : ℕ) (z : ℝ) => (switchLoss T (1 : ℝ) s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope T s : ℝ) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, hin, mul_comm]
    rw [hloss, iterate_affine_prefix]
    simp
  have hreg :
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T =
      -(∑ i ∈ range T, powerSteps α i * switchSlope T i *
        (∑ t ∈ Ico (i + 1) T, switchSlope T t)) := by
    unfold BanditRL.OnlineSubgradientDescent.regret
    simp only [EReal.toReal_coe]
    simp_rw [hrun]
    simp only [switchLoss, hin, mul_one, mul_zero, sub_zero]
    calc
      _ = -(∑ t ∈ Ico 0 T, ∑ i ∈ Ico 0 t,
          powerSteps α i * switchSlope T i * switchSlope T t) := by
        simp only [Nat.Ico_zero_eq_range, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -(∑ i ∈ range T, powerSteps α i * switchSlope T i *
          (∑ t ∈ Ico (i + 1) T, switchSlope T t)) := by
        rw [← Finset.sum_Ico_Ico_comm' 0 T
          (fun i t => powerSteps α i * switchSlope T i * switchSlope T t)]
        simp only [Nat.Ico_zero_eq_range, Finset.mul_sum]
  have hfirst : -(∑ i ∈ range m, powerSteps α i * switchSlope T i *
      (∑ t ∈ Ico (i + 1) T, switchSlope T t)) =
      (∑ i ∈ range m, ((i + 1 : ℕ) : ℝ) * powerSteps α i) -
        ((m : ℝ) - (k : ℝ)) * (∑ i ∈ range m, powerSteps α i) := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [hsuf i (him.trans_le hmT),
      show switchSlope T i = -1 by change (if i < m then (-1 : ℝ) else 1) = -1; exact if_pos him,
      min_eq_left (Nat.succ_le_of_lt him)]
    push_cast
    rw [hcast]
    ring
  have hlast : -(∑ i ∈ Ico m T, powerSteps α i * switchSlope T i *
      (∑ t ∈ Ico (i + 1) T, switchSlope T t)) =
      (∑ i ∈ Ico m T, ((i + 1 : ℕ) : ℝ) * powerSteps α i) -
        (T : ℝ) * (∑ i ∈ Ico m T, powerSteps α i) := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have him : m ≤ i := (Finset.mem_Ico.mp hi).1
    rw [hsuf i (Finset.mem_Ico.mp hi).2,
      show switchSlope T i = 1 by change (if i < m then (-1 : ℝ) else 1) = 1; exact if_neg (not_lt.mpr him),
      min_eq_right (him.trans (Nat.le_succ i))]
    push_cast
    ring
  have hpow (i : ℕ) : ((i + 1 : ℕ) : ℝ) * powerSteps α i =
      ((i + 1 : ℕ) : ℝ) ^ (1 - α) := by
    unfold powerSteps
    rw [show 1 - α = 1 + (-α) by ring,
      Real.rpow_add (by exact_mod_cast Nat.succ_pos i), Real.rpow_one]
  calc
    _ = -(∑ i ∈ range m, powerSteps α i * switchSlope T i *
          (∑ t ∈ Ico (i + 1) T, switchSlope T t)) -
        (∑ i ∈ Ico m T, powerSteps α i * switchSlope T i *
          (∑ t ∈ Ico (i + 1) T, switchSlope T t)) := by
      rw [hreg, ← Finset.sum_range_add_sum_Ico _ hmT]
      ring
    _ = -((m : ℝ) - (k : ℝ)) * (∑ i ∈ range m, powerSteps α i) +
        (∑ i ∈ range T, ((i + 1 : ℕ) : ℝ) ^ (1 - α)) -
        (T : ℝ) * (∑ i ∈ Ico m T, powerSteps α i) := by
      rw [sub_eq_add_neg, hfirst, hlast]
      rw [← Finset.sum_range_add_sum_Ico (fun i => ((i + 1 : ℕ) : ℝ) ^ (1 - α)) hmT]
      simp_rw [← hpow]
      ring

end BanditRL.OnlineUnboundedOSD

namespace BanditRL.OnlineUnboundedOSD

theorem switching_scalar_lower_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) :
    (1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
      (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T := by
  classical
  let β : ℝ := 1 - α
  let m : ℕ := (T + 1) / 2
  let k : ℕ := T / 2
  have hb0 : 0 < β := by dsimp [β]; linarith
  have hb1 : β < 1 := by dsimp [β]; linarith
  have hbp : 0 < β + 1 := by linarith
  have hφ := phi_range α hα0 hα1
  have hφ1 : phi α < 1 := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hden : 0 < β * phi α := mul_pos hb0 hφ.1
  have hden1 : β * phi α < 1 :=
    (mul_lt_mul_of_pos_right hb1 hφ.1).trans (by simpa using hφ1)
  have hth : 2 ≤ (T : ℝ) * (β * phi α) := (div_le_iff₀ hden).mp hT
  have hT2 : 2 ≤ T := by
    by_contra hn
    have hn1 : T ≤ 1 := by omega
    have hnR : (T : ℝ) ≤ 1 := by exact_mod_cast hn1
    have hmul := mul_le_mul_of_nonneg_right hnR hden.le
    nlinarith
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hmT : m ≤ T := by dsimp [m]; omega
  have hmhalf : (T : ℝ) / 2 ≤ (m : ℝ) := by
    have hn : T ≤ 2 * m := by dsimp [m]; omega
    have h : (T : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hn
    linarith
  have hdiff0 : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
    have h : k ≤ m := by dsimp [m, k]; omega
    exact sub_nonneg.mpr (by exact_mod_cast h)
  have hdiff1 : (m : ℝ) - (k : ℝ) ≤ 1 := by
    have h : m ≤ k + 1 := by dsimp [m, k]; omega
    have hR : (m : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hanti (a b : ℕ) (ha : 1 ≤ a) :
      AntitoneOn (fun x : ℝ => x ^ (-α)) (Set.Icc (a : ℝ) b) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hα0.le)).mono
    intro x hx
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    exact lt_of_lt_of_le (by norm_num) (haR.trans hx.1)
  have hsumfirst : (∑ i ∈ range m, powerSteps α i) ≤
      1 + ((m : ℝ) ^ β - 1) / β := by
    have h := (hanti 1 m (by omega)).sum_le_integral_Ico hm1
    rw [integral_rpow (Or.inl (by linarith : -1 < -α))] at h
    simp only [show -α + 1 = β by dsimp [β]; ring, Nat.cast_one, Real.one_rpow] at h
    have he := Finset.sum_range_add_sum_Ico (powerSteps α) hm1
    have hz : (∑ i ∈ range 1, powerSteps α i) = 1 := by norm_num [powerSteps]
    rw [hz] at he
    change (∑ i ∈ Ico 1 m, powerSteps α i) ≤ _ at h
    linarith
  have hsummain : (T : ℝ) ^ (β + 1) / (β + 1) ≤
      ∑ i ∈ range T, ((i + 1 : ℕ) : ℝ) ^ β := by
    have hm : MonotoneOn (fun x : ℝ => x ^ β) (Set.Icc (0 : ℝ) T) :=
      (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hb0.le).mono
        (fun x hx => hx.1)
    have hm' : MonotoneOn (fun x : ℝ => x ^ β) (Set.Icc ((0 : ℕ) : ℝ) T) := by simpa using hm
    have h := hm'.integral_le_sum_Ico (Nat.zero_le T)
    rw [integral_rpow (Or.inl (by linarith : -1 < β)), Nat.cast_zero,
      Real.zero_rpow hbp.ne', sub_zero, Nat.Ico_zero_eq_range] at h
    exact h
  have hsumlast : (∑ i ∈ Ico m T, powerSteps α i) ≤
      ((T : ℝ) ^ β - (m : ℝ) ^ β) / β := by
    have h := (hanti m T hm1).sum_le_integral_Ico hmT
    rw [integral_rpow (Or.inl (by linarith : -1 < -α))] at h
    simpa only [show -α + 1 = β by dsimp [β]; ring, powerSteps] using h
  have hSnonneg : 0 ≤ ∑ i ∈ range m, powerSteps α i :=
    Finset.sum_nonneg (fun i hi => (powerSteps_pos α i).le)
  have hc : ((m : ℝ) - (k : ℝ)) * (∑ i ∈ range m, powerSteps α i) ≤
      1 + ((m : ℝ) ^ β - 1) / β := by
    calc
      _ ≤ 1 * (∑ i ∈ range m, powerSteps α i) :=
        mul_le_mul_of_nonneg_right hdiff1 hSnonneg
      _ ≤ _ := by simpa using hsumfirst
  have hlast := mul_le_mul_of_nonneg_left hsumlast hTpos.le
  have hreg : -1 - ((m : ℝ) ^ β - 1) / β +
      (T : ℝ) ^ (β + 1) / (β + 1) -
      (T : ℝ) * (((T : ℝ) ^ β - (m : ℝ) ^ β) / β) ≤
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T := by
    rw [switching_scalar_regret_identity]
    change _ ≤ -((m : ℝ) - (k : ℝ)) * (∑ i ∈ range m, powerSteps α i) +
      (∑ i ∈ range T, ((i + 1 : ℕ) : ℝ) ^ β) -
      (T : ℝ) * (∑ i ∈ Ico m T, powerSteps α i)
    linarith
  have hpupper : (m : ℝ) ^ β ≤ (T : ℝ) ^ β :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmT) hb0.le
  have hplower : ((T : ℝ) / 2) ^ β ≤ (m : ℝ) ^ β :=
    Real.rpow_le_rpow (by positivity) hmhalf hb0.le
  have hinv : 0 ≤ -1 + 1 / β := by
    have h : β ≤ 1 := hb1.le
    have h' : (1 : ℝ) ≤ 1 / β := (le_div_iff₀ hb0).mpr (by simpa using h)
    linarith
  have hmdiv := div_le_div_of_nonneg_right hpupper hb0.le
  have hldiv := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sub_le_sub_left hplower ((T : ℝ) ^ β)) hb0.le) hTpos.le
  have happrox : -(T : ℝ) ^ β / β + (T : ℝ) ^ (β + 1) / (β + 1) -
      (T : ℝ) * (((T : ℝ) ^ β - ((T : ℝ) / 2) ^ β) / β) ≤
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T := by
    have he : ((m : ℝ) ^ β - 1) / β = (m : ℝ) ^ β / β - 1 / β := by ring
    rw [he] at hreg
    linear_combination hreg + hmdiv + hldiv + hinv
  have hphi : phi α = 1 / (β + 1) + ((1 / 2 : ℝ) ^ β - 1) / β := by
    unfold phi
    rw [show 1 - α = β by rfl, show 2 - α = β + 1 by dsimp [β]; ring]
  have hpow : (T : ℝ) ^ (β + 1) = (T : ℝ) ^ β * (T : ℝ) := by
    rw [Real.rpow_add hTpos, Real.rpow_one]
  have halgebra : -(T : ℝ) ^ β / β + (T : ℝ) ^ (β + 1) / (β + 1) -
      (T : ℝ) * (((T : ℝ) ^ β - ((T : ℝ) / 2) ^ β) / β) =
      -(T : ℝ) ^ β / β + phi α * (T : ℝ) ^ (β + 1) := by
    rw [hphi, hpow, show (T : ℝ) / 2 = (T : ℝ) * (1 / 2) by ring,
      Real.mul_rpow hTpos.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring
  rw [halgebra] at happrox
  have hcoef : 1 / β ≤ (1 / 2 : ℝ) * phi α * (T : ℝ) := by
    apply (div_le_iff₀ hb0).mpr
    nlinarith [hth]
  have hmul := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hTpos.le β)
  rw [show 2 - α = β + 1 by dsimp [β]; ring, hpow]
  rw [hpow] at happrox
  linear_combination happrox + hmul

end BanditRL.OnlineUnboundedOSD

namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem switching_vector_lower_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) (v : E) (hv : ‖v‖ = 1) :
    (1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T v t z : EReal)) 0 0 T := by
  classical
  have hin (a b : ℝ) : inner ℝ a b = b * a := rfl
  have hvec (t : ℕ) :
      BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun s z => (switchLoss T v s z : EReal)) 0 t =
      (-(∑ i ∈ range t, powerSteps α i * switchSlope T i)) • v := by
    have hloss : (fun s z => (switchLoss T v s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope T s • v) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, real_inner_smul_left]
    rw [hloss, iterate_affine_prefix]
    simp only [zero_sub, smul_smul, ← Finset.sum_smul, neg_smul]
  have hscalar (t : ℕ) :
      BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 t =
      -(∑ i ∈ range t, powerSteps α i * switchSlope T i) := by
    have hloss : (fun (s : ℕ) (z : ℝ) => (switchLoss T (1 : ℝ) s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope T s : ℝ) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, hin, mul_comm]
    rw [hloss, iterate_affine_prefix]
    simp
  have hreg : BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
      (fun t z => (switchLoss T v t z : EReal)) 0 0 T =
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T := by
    unfold BanditRL.OnlineSubgradientDescent.regret
    simp only [EReal.toReal_coe]
    simp_rw [hvec, hscalar]
    apply Finset.sum_congr rfl
    intro t ht
    simp [switchLoss, inner_smul_right, real_inner_self_eq_norm_sq, hv, hin]
  rw [hreg]
  exact switching_scalar_lower_bound α hα0 hα1 T hT

end BanditRL.OnlineUnboundedOSD

namespace BanditRL.OnlineUnboundedOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem theorem_5_4 [Nontrivial E] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) :
    ∃ loss : ℕ → E → ℝ,
      (∀ t < T, ConvexOn ℝ univ (loss t) ∧ LipschitzWith 1 (loss t)) ∧
      (1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
        BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
          (fun t z => (loss t z : EReal)) 0 0 T := by
  obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  refine ⟨switchLoss T v, ?_, switching_vector_lower_bound α hα0 hα1 T hT v hv⟩
  intro t ht
  exact switching_loss_regular T v hv t

end BanditRL.OnlineUnboundedOSD
