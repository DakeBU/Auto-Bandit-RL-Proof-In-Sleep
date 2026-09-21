import BanditRLProof.HeavyTailTuning

/-! An explicit integer sample budget makes twice the chosen radius smaller than the gap. -/
namespace BanditRLProof.HeavyTail

noncomputable def gapThreshold (ε u gap : ℝ) (T : ℕ) : ℕ :=
  Nat.ceil (confidenceLog T / (gap / (16*u^(1/(1+ε))))^((1+ε)/ε)) + 1

theorem gapThreshold_pos (ε u gap : ℝ) (T : ℕ) : 0 < gapThreshold ε u gap T := by
  exact Nat.succ_pos _

theorem confidenceLog_mono {t T : ℕ} (ht : t ≤ T) : confidenceLog t ≤ confidenceLog T := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  exact Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    (max_le_max (Nat.cast_le.mpr ht) le_rfl)

theorem twice_radius_lt_gap (ε u gap : ℝ) (hε : 0 < ε) (hu : 0 < u) (hg : 0 < gap)
    (t T n : ℕ) (ht : t ≤ T) (hn : gapThreshold ε u gap T ≤ n) :
    2 * confidenceRadius ε u t n < gap := by
  let A := 16*u^(1/(1+ε))
  let D := (gap/A)^((1+ε)/ε)
  have hA : 0 < A := mul_pos (by norm_num) (Real.rpow_pos_of_pos hu _)
  have hD : 0 < D := Real.rpow_pos_of_pos (div_pos hg hA) _
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr ((gapThreshold_pos ε u gap T).trans_le hn)
  have hceil := Nat.le_ceil (confidenceLog T / D)
  have hn' : (Nat.ceil (confidenceLog T / D) : ℝ) + 1 ≤ n := by
    exact_mod_cast hn
  have hlarge : confidenceLog T / D < n := by linarith
  have hLT : confidenceLog T < n*D := (div_lt_iff₀ hD).mp hlarge
  have hfrac : confidenceLog t / n < D := (div_lt_iff₀ hN).mpr (by
    have h := confidenceLog_mono ht
    nlinarith)
  have hq : 0 < ε/(1+ε) := div_pos hε (by linarith)
  have hpow := Real.rpow_lt_rpow (div_pos (confidenceLog_pos t) hN).le hfrac hq
  have hcancel : D^(ε/(1+ε)) = gap/A := by
    dsimp [D]
    rw [← Real.rpow_mul (div_pos hg hA).le]
    have he : ((1+ε)/ε)*(ε/(1+ε)) = (1 : ℝ) := by field_simp
    rw [he, Real.rpow_one]
  rw [hcancel] at hpow
  have h := mul_lt_mul_of_pos_left hpow hA
  have he : A * (gap/A) = gap := by field_simp
  rw [he] at h
  unfold confidenceRadius
  dsimp [A] at h
  nlinarith

end BanditRLProof.HeavyTail
