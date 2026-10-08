from append_leaf_v1 import *
assert load(RUN/'D2-attempt-v1.json')['actual_build_exit']==0
helpers='''private theorem dyadic_pair (k : ℕ) :
    dyadicObservation (2*k+1) = 1 - dyadicObservation k ∧
    dyadicObservation (2*k+2) = 1 - dyadicObservation k := by
  constructor
  · have hd : (2*k) / 2 = k := by omega
    rw [dyadicObservation, hd]
  · have he : 2*k+2 = (2*k+1)+1 := by omega
    have hd : (2*k+1) / 2 = k := by omega
    rw [he, dyadicObservation, hd]

private theorem dyadic_prefix_pair (n : ℕ) :
    (∑ t ∈ Finset.range (2*n+1), dyadicObservation t) =
      2*(n : ℝ) - 2*(∑ t ∈ Finset.range n, dyadicObservation t) := by
  induction n with
  | zero => simp [dyadicObservation]
  | succ n ih =>
    have hidx : 2*(n+1)+1 = ((2*n+1)+1)+1 := by omega
    have hsec : (2*n+1)+1 = 2*n+2 := by omega
    rw [hidx, Finset.sum_range_succ dyadicObservation ((2*n+1)+1),
      Finset.sum_range_succ dyadicObservation (2*n+1), ih, hsec,
      (dyadic_pair n).1, (dyadic_pair n).2,
      Finset.sum_range_succ dyadicObservation n]
    push_cast
    ring

private theorem dyadic_high_count (n : ℕ) :
    (∑ t ∈ Finset.range (4^n-1), dyadicObservation t) =
      ((2 : ℝ)/3) * ((4 : ℝ)^n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1 ≤ (4 : ℕ)^n := Nat.one_le_pow n 4 (by omega)
    have hidx : (4 : ℕ)^(n+1)-1 = 2*(2*(4^n-1)+1)+1 := by
      rw [pow_succ]
      omega
    rw [hidx, dyadic_prefix_pair, dyadic_prefix_pair, ih]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_one,
      Nat.cast_ofNat, Nat.cast_pow, pow_succ]
    ring

private theorem dyadic_low_count (n : ℕ) :
    (∑ t ∈ Finset.range (2*4^n-1), dyadicObservation t) =
      ((2 : ℝ)/3) * ((4 : ℝ)^n - 1) := by
  have hp : 1 ≤ (4 : ℕ)^n := Nat.one_le_pow n 4 (by omega)
  have hidx : 2*(4 : ℕ)^n-1 = 2*(4^n-1)+1 := by omega
  rw [hidx, dyadic_prefix_pair, dyadic_high_count]
  simp only [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  ring

private theorem dyadic_high_mean (n : ℕ) :
    empiricalMean dyadicObservation (4^(n+1)-1) = (2 : ℝ)/3 := by
  have hp : 1 ≤ (4 : ℕ)^(n+1) := Nat.one_le_pow (n+1) 4 (by omega)
  have hpos : 1 < (4 : ℕ)^(n+1) := by
    have hn := Nat.one_le_pow n 4 (by omega)
    rw [pow_succ]
    omega
  have hd : ((4 : ℝ)^(n+1)-1) ≠ 0 := by
    have hR : (1 : ℝ) < 4^(n+1) := by exact_mod_cast hpos
    linarith
  unfold empiricalMean
  rw [dyadic_high_count]
  simp only [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  exact mul_div_cancel_right₀ _ hd

private theorem dyadic_low_mean (n : ℕ) :
    empiricalMean dyadicObservation (2*4^n-1) =
      (1 : ℝ)/3 - ((1 : ℝ)/3) / ((2*4^n-1 : ℕ) : ℝ) := by
  have hp : 1 ≤ (4 : ℕ)^n := Nat.one_le_pow n 4 (by omega)
  have htwo : 1 ≤ 2*(4 : ℕ)^n := by omega
  have hpos : 0 < 2*(4 : ℕ)^n-1 := by omega
  have hcast : ((2*4^n-1 : ℕ) : ℝ) = 2*(4 : ℝ)^n-1 := by
    simp only [Nat.cast_sub htwo, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  have hd : 2*(4 : ℝ)^n-1 ≠ 0 := by
    rw [← hcast]
    exact_mod_cast Nat.ne_of_gt hpos
  unfold empiricalMean
  rw [dyadic_low_count, hcast]
  field_simp
  ring

private theorem dyadic_horizons_tendsto :
    Tendsto (fun n : ℕ => 4^(n+1)-1) atTop atTop ∧
    Tendsto (fun n : ℕ => 2*4^n-1) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (4 : ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  constructor
  · apply tendsto_atTop.2
    intro b
    filter_upwards [hp.eventually (eventually_ge_atTop (b+1))] with n hn
    rw [pow_succ]
    omega
  · apply tendsto_atTop.2
    intro b
    filter_upwards [hp.eventually (eventually_ge_atTop (b+1))] with n hn
    omega
'''
body=''' := by
  constructor
  · have heq : (fun n : ℕ => empiricalMean dyadicObservation (4^(n+1)-1)) =
        fun _ : ℕ => (2 : ℝ)/3 := funext dyadic_high_mean
    rw [heq]
    exact tendsto_const_nhds
  · have ht : Tendsto (fun n : ℕ => ((2*4^n-1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp dyadic_horizons_tendsto.2
    have hz : Tendsto (fun n : ℕ => ((2*4^n-1 : ℕ) : ℝ)⁻¹) atTop (nhds (0 : ℝ)) :=
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp ht
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)/3)
      atTop (nhds ((1 : ℝ)/3))).sub (hz.const_mul ((1 : ℝ)/3))
    simp only [mul_zero, sub_zero] at hh
    apply hh.congr'
    apply Eventually.of_forall
    intro n
    simpa only [div_eq_mul_inv] using (dyadic_low_mean n).symm
'''
append_leaf(2,body,helpers)
