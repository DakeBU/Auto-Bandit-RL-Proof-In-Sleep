import BanditRLProof.HOOPacking
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

/-! Definition 5 with the explicit extended-real log(0)=-infinity convention
frozen in LIPSCHITZ-HOO-CONTRACT.md before this implementation. -/
namespace BanditRLProof.HOO
open Filter Set
open scoped Topology

noncomputable def RegularCovering.nearOptimalPacking {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best c ε : ℝ) : ℕ :=
  C.packingNumber {x | best-f x ≤ c*ε} ε

/-- The normalized extended logarithm. At zero packing the value is minus
infinity; this does not invoke the totalized real logarithm at zero. -/
noncomputable def packingExponent (N : ℕ) (ε : ℝ) : EReal :=
  if N=0 then ⊥ else (Real.log (N:ℝ) / Real.log (1/ε) : ℝ)

@[simp] theorem packingExponent_zero (ε : ℝ) : packingExponent 0 ε = ⊥ := by
  simp [packingExponent]

theorem packingExponent_positive {N : ℕ} (hN : 0<N) (ε : ℝ) :
    packingExponent N ε = (Real.log (N:ℝ) / Real.log (1/ε) : ℝ) := by
  simp [packingExponent, Nat.ne_of_gt hN]

noncomputable def RegularCovering.nearOptimalityDimension {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best c : ℝ) : EReal :=
  max 0 (limsup (fun ε => packingExponent (C.nearOptimalPacking f best c ε) ε) (𝓝[>] 0))

theorem RegularCovering.nearOptimalityDimension_nonneg {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best c : ℝ) :
    0 ≤ C.nearOptimalityDimension f best c := le_max_left _ _

theorem packing_le_rpow_of_exponent_lt {N : ℕ} {ε d : ℝ}
    (hε : 0<ε) (hε1 : ε<1) (h : packingExponent N ε < (d:EReal)) :
    (N:ℝ) ≤ ε^(-d) := by
  by_cases hN : N=0
  · simp only [hN, Nat.cast_zero]
    exact (Real.rpow_pos_of_pos hε _).le
  have hp : 0 < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hl : 0 < Real.log (1/ε) := Real.log_pos ((one_lt_div hε).mpr hε1)
  have hh : Real.log (N:ℝ) / Real.log (1/ε) < d := by
    exact EReal.coe_lt_coe_iff.mp (by simpa only [packingExponent, if_neg hN] using h)
  apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos hε _)).mp
  rw [Real.log_rpow hε]
  have he : Real.log (1/ε) = -Real.log ε := by simp
  have hi := (div_lt_iff₀ hl).mp hh
  rw [he] at hi
  nlinarith

/-- Strictly exceeding the actual limsup dimension produces a fine-scale
packing bound; no power-law packing premise is assumed. -/
theorem RegularCovering.eventually_nearOptimalPacking_le {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best c d : ℝ)
    (hd : C.nearOptimalityDimension f best c < (d:EReal)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), (C.nearOptimalPacking f best c ε : ℝ) ≤ ε^(-d) := by
  have hl : limsup (fun ε => packingExponent (C.nearOptimalPacking f best c ε) ε)
      (𝓝[>] (0:ℝ)) < (d:EReal) := (le_max_right _ _).trans_lt hd
  filter_upwards [eventually_lt_of_limsup_lt hl,
    self_mem_nhdsWithin, eventually_lt_nhds (by norm_num : (0:ℝ)<1) |>.filter_mono nhdsWithin_le_nhds]
    with ε he hpos hlt
  exact packing_le_rpow_of_exponent_lt hpos hlt he


/-- Source Theorem 6's uniform constant, including all coarse scales up to R.
The fine-scale bound comes from Definition 5, the coarse bound from A1. -/
theorem RegularCovering.uniform_nearOptimalPacking_le {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best c d R : ℝ) (hR : 0<R)
    (hd : C.nearOptimalityDimension f best c < (d:EReal)) :
    ∃ K : ℝ, 0<K ∧ ∀ ε : ℝ, 0<ε → ε≤R →
      (C.nearOptimalPacking f best c ε : ℝ) ≤ K * ε^(-d) := by
  have hdpos : 0<d := EReal.coe_lt_coe_iff.mp
    ((C.nearOptimalityDimension_nonneg f best c).trans_lt hd)
  obtain ⟨δ, hδ, hfine⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (C.eventually_nearOptimalPacking_le f best c d hd)
  let M : ℝ := C.packingNumber Set.univ δ
  let K : ℝ := max 1 (M / R^(-d))
  have hK : 0<K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, hK, fun ε hε hεR => ?_⟩
  have hp : 0 < ε^(-d) := Real.rpow_pos_of_pos hε _
  by_cases he : ε<δ
  · exact (hfine ⟨hε, he⟩).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (M/R^(-d))) hp.le)
  · have hm : (C.nearOptimalPacking f best c ε : ℝ) ≤ M := by
      change (C.packingNumber {x | best-f x ≤ c*ε} ε : ℝ) ≤
        (C.packingNumber Set.univ δ : ℝ)
      exact_mod_cast C.packingNumber_le_ambient {x | best-f x ≤ c*ε} hδ (le_of_not_gt he)
    have hmK : M ≤ K * R^(-d) := (div_le_iff₀ (Real.rpow_pos_of_pos hR _)).mp
      (le_max_right _ _)
    exact hm.trans (hmK.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hε hεR (neg_nonpos.mpr hdpos.le)) hK.le))

/-- Actual near-optimal tree levels inherit the power bound at the exact
source parameter c=4*nu1/nu2. The constant is independent of depth. -/
theorem RegularCovering.nearOptimalNodes_power_bound {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best d : ℝ)
    (hw : WeaklyLipschitz f C.ell best)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ K : ℝ, 0<K ∧ ∀ h : ℕ,
      ((C.nearOptimalNodes f best h).card : ℝ) ≤ K * (C.nu2*C.rho^h)^(-d) := by
  obtain ⟨K, hK, hbound⟩ := C.uniform_nearOptimalPacking_le f best (4*C.nu1/C.nu2)
    d C.nu2 C.nu2_pos hd
  refine ⟨K, hK, fun h => ?_⟩
  have heq : (4*C.nu1/C.nu2)*(C.nu2*C.rho^h) = 4*(C.nu1*C.rho^h) := by
    field_simp [ne_of_gt C.nu2_pos]
  have hi : ((C.nearOptimalNodes f best h).card : ℝ) ≤
      (C.nearOptimalPacking f best (4*C.nu1/C.nu2) (C.nu2*C.rho^h) : ℝ) := by
    unfold nearOptimalPacking
    rw [heq]
    exact_mod_cast C.nearOptimalNodes_card_le_packing f best hw h
  exact hi.trans (hbound _ (mul_pos C.nu2_pos (pow_pos C.rho_pos _))
    (by
      simpa using mul_le_mul_of_nonneg_left
        (pow_le_one₀ C.rho_pos.le C.rho_lt_one.le (n := h)) C.nu2_pos.le))

end BanditRLProof.HOO

