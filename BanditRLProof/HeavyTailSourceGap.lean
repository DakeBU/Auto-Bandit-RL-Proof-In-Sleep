import BanditRLProof.Algorithms.HeavyTailSourcePolicy

/-! Explicit corrected gap cutoff for the unchanged source-parameter policy. -/
namespace BanditRLProof.HeavyTail.SourcePolicy

noncomputable def horizonLog (T : ℕ) : ℝ := 2*Real.log (max (T : ℝ) 1)

noncomputable def gapBudget (ε u gap : ℝ) (T : ℕ) : ℝ :=
  horizonLog T / (gap / (8*u^(1/(1+ε))))^((1+ε)/ε)

noncomputable def gapThreshold (ε u gap : ℝ) (T : ℕ) : ℕ :=
  Nat.ceil (gapBudget ε u gap T)

theorem horizonLog_nonneg (T : ℕ) : 0 ≤ horizonLog T :=
  mul_nonneg (by norm_num) (Real.log_nonneg (le_max_right _ _))

theorem horizonLog_pos (T : ℕ) (hT : 2 ≤ T) : 0 < horizonLog T := by
  apply mul_pos (by norm_num) (Real.log_pos _)
  have h : (2 : ℝ) ≤ T := by exact_mod_cast hT
  exact lt_of_lt_of_le (by linarith : (1 : ℝ) < T) (le_max_left _ _)

theorem gapBudget_nonneg (ε u gap : ℝ) (T : ℕ) (hu : 0 < u) (hg : 0 < gap) :
    0 ≤ gapBudget ε u gap T := by
  exact div_nonneg (horizonLog_nonneg T) (Real.rpow_pos_of_pos
    (div_pos hg (mul_pos (by norm_num) (Real.rpow_pos_of_pos hu _))) _).le

theorem gapThreshold_pos (ε u gap : ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hu : 0 < u) (hg : 0 < gap) : 0 < gapThreshold ε u gap T := by
  apply Nat.ceil_pos.mpr
  exact div_pos (horizonLog_pos T hT) (Real.rpow_pos_of_pos
    (div_pos hg (mul_pos (by norm_num) (Real.rpow_pos_of_pos hu _))) _)

theorem sourceLog_le_horizon {t T : ℕ} (ht : t < T) : sourceConfidenceLog t ≤ horizonLog T := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.log_le_log (by positivity : (0 : ℝ) < t+1)
  apply le_trans _ (le_max_left (T : ℝ) 1)
  exact_mod_cast ht

theorem twice_radius_le_gap (ε u gap : ℝ) (hε : 0 < ε) (hu : 0 < u) (hg : 0 < gap)
    (t T n : ℕ) (hT : 2 ≤ T) (ht : t < T) (hn : gapThreshold ε u gap T ≤ n) :
    2*sourceConfidenceRadius ε u t n ≤ gap := by
  let A := 8*u^(1/(1+ε))
  let D := (gap/A)^((1+ε)/ε)
  have hA : 0 < A := mul_pos (by norm_num) (Real.rpow_pos_of_pos hu _)
  have hD : 0 < D := Real.rpow_pos_of_pos (div_pos hg hA) _
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr
    ((gapThreshold_pos ε u gap T hT hu hg).trans_le hn)
  have hlarge : horizonLog T / D ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hLT : horizonLog T ≤ n*D := (div_le_iff₀ hD).mp hlarge
  have hfrac : sourceConfidenceLog t / n ≤ D := (div_le_iff₀ hN).mpr (by
    have h := sourceLog_le_horizon ht
    nlinarith)
  have hq : 0 < ε/(1+ε) := div_pos hε (by linarith)
  have hL0 : 0 ≤ sourceConfidenceLog t :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith))
  have hpow := Real.rpow_le_rpow (div_nonneg hL0 hN.le) hfrac hq.le
  have hcancel : D^(ε/(1+ε)) = gap/A := by
    dsimp [D]
    rw [← Real.rpow_mul (div_pos hg hA).le]
    have he : ((1+ε)/ε)*(ε/(1+ε)) = (1 : ℝ) := by field_simp
    rw [he, Real.rpow_one]
  rw [hcancel] at hpow
  have h := mul_le_mul_of_nonneg_left hpow hA.le
  have he : A*(gap/A) = gap := by field_simp
  rw [he] at h
  unfold sourceConfidenceRadius
  dsimp [A] at h
  nlinarith

end BanditRLProof.HeavyTail.SourcePolicy
