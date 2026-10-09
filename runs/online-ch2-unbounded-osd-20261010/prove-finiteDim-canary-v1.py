from canary_driver import *
assert load(RUN/'scalar_actual_two_rounds-fence-compared-v1.json')['unchanged']
lower_canary(1,'''  classical
  have hv : ‖direction‖ = 1 := by simp [direction]
  have hx1 : vectorRun 64 1 = direction := by
    have hloss : (fun s z => (switchLoss 64 direction s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope 64 s • direction) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, real_inner_smul_left]
    unfold vectorRun
    rw [hloss, iterate_affine_prefix]
    norm_num [sum_range_succ, powerSteps, switchSlope]
  have hregular : ∀ t < 64, ConvexOn ℝ univ (switchLoss 64 direction t) ∧
      LipschitzWith 1 (switchLoss 64 direction t) := by
    intro t ht
    exact switching_loss_regular 64 direction hv t
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (7/5 : ℝ) < Real.sqrt 2 := by nlinarith
  have hh : (1/2 : ℝ) ^ (1/2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  have hphi_eq : phi (1/2) = Real.sqrt 2 - 4/3 := by
    unfold phi
    norm_num only [show 2 - (1/2 : ℝ) = 3/2 by norm_num,
      show 1 - (1/2 : ℝ) = 1/2 by norm_num]
    rw [hh]
    field_simp [ne_of_gt hspos]
    nlinarith [hsq]
  have hphi : (1/15 : ℝ) ≤ phi (1/2) := by rw [hphi_eq]; linarith
  have hp : 0 < phi (1/2) := (phi_range (1/2) (by norm_num) (by norm_num)).1
  have hthreshold : 2 / ((1 - (1/2 : ℝ)) * phi (1/2)) ≤ (64 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1 - 1/2) hp)).mpr
    nlinarith [hphi]
  have hprinted : (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤
      vectorRegret 64 :=
    switching_vector_lower_bound (1/2) (by norm_num) (by norm_num) 64 hthreshold direction hv
  have hpower : (64 : ℝ) ^ (2 - (1/2 : ℝ)) = 512 := by
    rw [show 2 - (1/2 : ℝ) = 1 + (1/2) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 64), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    norm_num
  have hlow : (256/15 : ℝ) ≤ vectorRegret 64 := by
    have hcompare : (256/15 : ℝ) ≤ (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) := by
      rw [hpower]
      linarith [hphi]
    exact hcompare.trans hprinted
  have hstrict : (17 : ℝ) < vectorRegret 64 :=
    lt_of_lt_of_le (by norm_num : (17 : ℝ) < 256/15) hlow
  have hex := theorem_5_4 (E := EuclideanSpace ℝ (Fin 2))
    (1/2) (by norm_num) (by norm_num) 64 hthreshold
  exact ⟨hv, hx1, hregular, hphi, hthreshold, hprinted, hlow, hstrict, hex⟩
''')
write(RUN/'two-canaries-local-milestone-v1.json',dict(full_conjunction_sizes=[7,9],status='Actual focused compiled/fenced; BODY/value audit/full project gates open',different_horizon_loss_streams=True,nonzero_finiteDim_source_lower_bound='256/15<=actual regret and17<actual regret at64',source_existential_fully_applied=True,package_accepted=False,chapter_complete=False,whole_Goal='ACTIVE'))
