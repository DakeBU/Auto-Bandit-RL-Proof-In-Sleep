import BanditRLProof.OnlineFTLLimitSemantics
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
namespace BanditRL.OnlineLearning

/-- Explicit binary dyadic-block observations, independent of the learner and horizon. -/
noncomputable def dyadicObservation : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 - dyadicObservation (n / 2)
termination_by n => n
decreasing_by omega


/-- Derived literal-limit criterion for the actual bounded squared-loss FTL. -/
theorem meanPredict_limitNoRegret_iff_mean_converges (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) :
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2) (meanPredict y) ↔
      ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean y) atTop (nhds m) := by
  constructor
  · intro hL
    rcases hL 0 (by norm_num) with ⟨a0, ha0, h0⟩
    rcases hL 1 (by norm_num) with ⟨a1, ha1, h1⟩
    have hs0 := (meanPredict_fixedRegret_limit_iff y hy 0 a0).mp h0
    have hs1 := (meanPredict_fixedRegret_limit_iff y hy 1 a1).mp h1
    let m : ℝ := (-a0 - (-a1) + 1) / 2
    have hh := ((hs0.sub hs1).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))).div_const (2 : ℝ)
    have hm : Tendsto (empiricalMean y) atTop (nhds m) := by
      convert hh using 1
      funext T
      ring
    have hb : ∀ᶠ T : ℕ in atTop, empiricalMean y T ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
      exact empiricalMean_mem y T hT (fun t _ => hy t)
    have hlo : 0 ≤ m := ge_of_tendsto hm (hb.mono (fun _ h => h.1))
    have hup : m ≤ 1 := le_of_tendsto hm (hb.mono (fun _ h => h.2))
    exact ⟨m, ⟨hlo, hup⟩, hm⟩
  · rintro ⟨m, hmUnit, hm⟩
    exact (meanPredict_limitNoRegret_of_mean_converges y hy m hm).2


private theorem dyadicObservation_binary (t : ℕ) :
    dyadicObservation t = 0 ∨ dyadicObservation t = 1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simp [dyadicObservation]
    | succ n =>
      have hparent : n / 2 < n + 1 := by omega
      rcases ih (n / 2) hparent with hzero | hone
      · rw [dyadicObservation, hzero]
        norm_num
      · rw [dyadicObservation, hone]
        norm_num

theorem dyadicObservation_unit :
    ∀ t, dyadicObservation t ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  rcases dyadicObservation_binary t with hzero | hone
  · simp [hzero]
  · simp [hone]


private theorem dyadic_pair (k : ℕ) :
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

theorem dyadic_empiricalMean_subsequences :
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (4^(n + 1) - 1))
      atTop (nhds ((2 : ℝ) / 3)) ∧
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (2 * 4^n - 1))
      atTop (nhds ((1 : ℝ) / 3)) := by
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



theorem dyadic_meanPredict_obstruction :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ∧
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) := by
  have hy := dyadicObservation_unit
  have hn : ¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a) := by
    rintro ⟨a, ha⟩
    have hs := (meanPredict_fixedRegret_limit_iff dyadicObservation hy 0 a).mp ha
    have hh := ((tendsto_const_nhds (x := (0 : ℝ))).sub dyadic_empiricalMean_subsequences.1).pow 2
    have hl := ((tendsto_const_nhds (x := (0 : ℝ))).sub dyadic_empiricalMean_subsequences.2).pow 2
    have eh : -a = ((0 : ℝ) - 2/3)^2 :=
      tendsto_nhds_unique (hs.comp dyadic_horizons_tendsto.1) hh
    have el : -a = ((0 : ℝ) - 1/3)^2 :=
      tendsto_nhds_unique (hs.comp dyadic_horizons_tendsto.2) hl
    norm_num at eh el
    linarith
  refine ⟨meanPredict_noRegret dyadicObservation hy,
    meanPredict_bestRegret_average_tendsto_zero dyadicObservation hy, hn, ?_⟩
  intro hL
  obtain ⟨a, ha, hlim⟩ := hL 0 (by norm_num)
  exact hn ⟨a, hlim⟩

end BanditRL.OnlineLearning
