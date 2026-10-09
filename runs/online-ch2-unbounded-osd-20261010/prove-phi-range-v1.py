from leaf_driver import *
assert load(RUN/'switching_loss_regular-fence-compared-v2.json')['unchanged']
lower('phi_range','''  let β : ℝ := 1 - α
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
    simpa using Real.rpow_one_add_lt_one_add_mul_self
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
      hconc.slope_le_of_hasDerivAt (by norm_num : (0 : ℝ) ∈ Icc 0 1)
        (show β ∈ Icc 0 1 from ⟨hb0.le, hb1.le⟩) hb0 (hd 0)
  constructor
  · rw [hphi]
    exact div_pos (sub_pos.mpr hq) (mul_pos hb0 hbp)
  · rw [hphi, div_lt_iff₀ (mul_pos hb0 hbp)]
    have hnum := (div_le_iff₀ hb0).mp hs
    have hc : 0 < (1 - Real.log 2) * β := mul_pos (sub_pos.mpr hl1) hb0
    nlinarith
''',['Real.rpow_one_add_lt_one_add_mul_self strict Bernoulli actual primary API','actual differentiated coefficient q on[0,1] and concave tangent bound','Real.log_two_lt_d9 actual primary API'])
write(RUN/'phi-range-local-milestone-v1.json',dict(leaf=targets['phi_range']['name'],status='focused compiled/frozen only',source_algorithm_lower_bound_open=True,package_BODY_accepted=False,whole_Goal='ACTIVE'))
