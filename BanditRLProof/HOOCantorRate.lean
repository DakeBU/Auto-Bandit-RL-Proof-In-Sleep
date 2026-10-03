import BanditRLProof.HOOCantorModel
import BanditRLProof.Algorithms.HOOActualRegret

/-! A conservative finite dimension certificate and full-rate instantiation
for the infinite-arm noisy Cantor model. The certificate is an upper bound,
not a claim that its exact near-optimality dimension equals two. -/
namespace BanditRLProof.HOO.CantorModel
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
set_option autoImplicit false

theorem packing_le_two_div (A : Set Arm) {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    (covering.packingNumber A ε : ℝ) ≤ 2/ε := by
  obtain ⟨h, hh, he⟩ := exists_nat_pow_near_of_lt_one hε hε1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨centers, hc⟩ := covering.packingNumber_attained A ε hε
  have hn : covering.packingNumber A ε ≤ 2^(h+1) := by
    simpa only [Fintype.card_fin] using covering.disjoint_ball_family_card_le centers ε (h+1)
      (by simpa only [covering, one_mul] using hh) hc.disjoint
  have hnR : (covering.packingNumber A ε : ℝ) ≤ (2:ℝ)^(h+1) := by exact_mod_cast hn
  have hid : (2:ℝ)^h * (1/2:ℝ)^h = 1 := by rw [← mul_pow]; norm_num
  apply (le_div_iff₀ hε).mpr
  have ha := mul_le_mul_of_nonneg_left he (by positivity : 0≤(2:ℝ)^(h+1))
  have hb := mul_le_mul_of_nonneg_right hnR hε.le
  rw [pow_succ] at ha hb
  nlinarith

/-- Conservative upper certificate, sufficient for a nonvacuous full-rate
canary. It follows from ambient packing, not a postulated dimension value. -/
theorem dimension_le_two (c : ℝ) :
    covering.nearOptimalityDimension mean (1/2) c ≤ (2:EReal) := by
  unfold RegularCovering.nearOptimalityDimension
  apply max_le (by norm_num)
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [self_mem_nhdsWithin,
    eventually_lt_nhds (by norm_num : (0:ℝ)<1/2) |>.filter_mono nhdsWithin_le_nhds]
    with ε hε he
  let k := covering.nearOptimalPacking mean (1/2) c ε
  by_cases hk : k=0
  · change packingExponent k ε ≤ (2:EReal)
    simp [hk]
  have hkpos : 0<(k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkbound : (k:ℝ) ≤ 2/ε := packing_le_two_div _ hε (by linarith)
  have hlog : 0<Real.log (1/ε) := Real.log_pos ((one_lt_div hε).mpr (by linarith))
  have heq : ε^(-(2:ℝ))=1/ε^2 := by
    rw [Real.rpow_neg hε.le]
    norm_num
  have hpower : (k:ℝ) ≤ ε^(-(2:ℝ)) := by
    rw [heq]
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    have hh := (le_div_iff₀ hε).mp hkbound
    have hm := mul_le_mul_of_nonneg_right hh hε.le
    nlinarith
  have hh := Real.log_le_log hkpos hpower
  rw [Real.log_rpow hε] at hh
  have hq : Real.log (k:ℝ)/Real.log (1/ε) ≤ 2 := by
    apply (div_le_iff₀ hlog).mpr
    simpa using hh
  change packingExponent k ε ≤ (2:EReal)
  simp only [packingExponent, if_neg hk]
  exact EReal.coe_le_coe_iff.mpr hq

/-- A concrete full-rate consequence with d'=3>dimension. The general theorem
retains every d' strictly above the actual dimension; this model certificate
is deliberately conservative and does not claim the sharp model exponent. -/
theorem expected_actual_rate : ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
    (∫ Y, (∑ n ∈ Finset.range N, ((1/2:ℝ)-Y n))
      ∂trajectory 1 (1/2) (covering.toCovering.nodeLaw law)) ≤
      γ*(N:ℝ)^(4/5:ℝ)*(Real.log (max (N:ℝ) 2))^(1/5:ℝ) := by
  have hr (x : Arm) : mean x ∈ Set.Icc (0:ℝ) 1 := by
    unfold mean; split_ifs <;> norm_num
  have hd : covering.nearOptimalityDimension mean (1/2) (4*covering.nu1/covering.nu2) < (3:EReal) :=
    (dimension_le_two _).trans_lt (by exact_mod_cast (by norm_num : (2:ℝ)<3))
  have he := covering.expected_actualRegret_rate law mean (1/2) 3 law_mean mean_le_best hr
    global_sup weaklyLipschitz law_bounded hd
  norm_num only [covering, one_mul, one_div, Nat.cast_ofNat, add_zero] at he ⊢
  convert he using 1

end BanditRLProof.HOO.CantorModel
