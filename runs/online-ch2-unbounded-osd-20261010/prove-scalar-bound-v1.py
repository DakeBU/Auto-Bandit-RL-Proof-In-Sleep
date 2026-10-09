from leaf_driver import *
assert load(RUN/'switching_scalar_regret_identity-fence-compared-v2.json')['unchanged']
assert load(RUN/'phi_range-fence-compared-v3.json')['unchanged']
lower('switching_scalar_lower_bound','''  classical
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
    simp only [show -α + 1 = β by dsimp [β]; ring, Real.one_rpow] at h
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
    have h := hm.integral_le_sum_Ico (Nat.zero_le T)
    rw [integral_rpow (Or.inl (by linarith : -1 < β)),
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
    linarith
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
  nlinarith
''',['switching_scalar_regret_identity actual same canonical OSD run','phi_range actual positivity','AntitoneOn.sum_le_integral_Ico/MonotoneOn.integral_le_sum_Ico actual primary APIs','integral_rpow actual primary API','exact frozen horizon threshold'])
write(RUN/'scalar-lower-bound-local-milestone-v1.json',dict(leaf=targets['switching_scalar_lower_bound']['name'],status='focused compiled/frozen only',actual_scalar_lower_bound_closed=True,vector_lift_open=True,full_source_theorem_open=True,package_BODY_accepted=False,whole_Goal='ACTIVE'))
