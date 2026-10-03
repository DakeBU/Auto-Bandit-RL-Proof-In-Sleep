import BanditRLProof.HeavyTailPowerSum
import BanditRLProof.Algorithms.HeavyTailUCB

/-! Algebraic tuning for the sample-index threshold; all exponents remain real. -/
namespace BanditRLProof.HeavyTail

theorem power_threshold_bias_term (u c a ε x : ℝ) (hc : 0 < c) (hx : 0 < x)
    (haε : a * ε = 1-a) :
    u / (c * x^a)^ε = (u / c^ε) * x^(a-1) := by
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le,
    haε]
  rw [show a-1 = -(1-a) by ring, Real.rpow_neg hx.le]
  ring

theorem power_threshold_bias_sum (u c a ε : ℝ) (hu : 0 ≤ u) (hc : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) (haε : a * ε = 1-a) (n : ℕ) :
    (∑ s ∈ Finset.range n, u / (c * ((s : ℝ)+1)^a)^ε) ≤
      (u / c^ε) * ((n : ℝ)^a / a) := by
  have hterm : ∀ s : ℕ, u / (c * ((s : ℝ)+1)^a)^ε =
      (u / c^ε) * ((s : ℝ)+1)^(a-1) := fun s =>
    power_threshold_bias_term u c a ε _ hc (by positivity) haε
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_shifted_rpow_le a ha ha1 n)
    (div_nonneg hu (Real.rpow_nonneg hc.le _))

theorem sampleThreshold_factor (ε u : ℝ) (hu : 0 ≤ u) (t s : ℕ) :
    sampleThreshold ε u t s =
      (u / confidenceLog t)^(1/(1+ε)) * ((s : ℝ)+1)^(1/(1+ε)) := by
  have hL : 0 < confidenceLog t := by
    unfold confidenceLog
    exact mul_pos (by norm_num) (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  unfold sampleThreshold
  rw [show u * ((s : ℝ)+1) / confidenceLog t =
      (u / confidenceLog t) * ((s : ℝ)+1) by ring]
  exact Real.mul_rpow (div_nonneg hu hL.le) (by positivity)

theorem sampleThreshold_bias_sum (ε u : ℝ) (hε : 0 ≤ ε) (hu : 0 < u) (t n : ℕ) :
    (∑ s ∈ Finset.range n, u / (sampleThreshold ε u t s)^ε) ≤
      (u / ((u / confidenceLog t)^(1/(1+ε)))^ε) *
        ((n : ℝ)^(1/(1+ε)) / (1/(1+ε))) := by
  have hp : 0 < 1+ε := by linarith
  have hL : 0 < confidenceLog t := by
    unfold confidenceLog
    exact mul_pos (by norm_num) (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  simp_rw [sampleThreshold_factor ε u hu.le]
  apply power_threshold_bias_sum u _ _ ε hu.le
    (Real.rpow_pos_of_pos (div_pos hu hL) _) (one_div_pos.mpr hp)
    ((div_le_one hp).mpr (by linarith))
  field_simp
  ring

theorem power_scale_bias (u L a ε : ℝ) (hu : 0 < u) (hL : 0 < L)
    (haε : a * ε = 1-a) :
    u / ((u/L)^a)^ε = u^a * L^(1-a) := by
  rw [← Real.rpow_mul (div_pos hu hL).le, haε, Real.div_rpow hu.le hL.le]
  have he : u / u^(1-a) = u^a := by
    apply (div_eq_iff (Real.rpow_pos_of_pos hu _).ne').mpr
    rw [← Real.rpow_add hu, add_sub_cancel, Real.rpow_one]
  calc
    u / (u^(1-a) / L^(1-a)) = (u / u^(1-a)) * L^(1-a) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
    _ = u^a * L^(1-a) := by rw [he]

theorem power_bias_normalization (u L a N : ℝ) (hL : 0 < L) (hN : 0 < N) :
    (u^a * L^(1-a)) * (N^a / a) / N =
      (1/a) * u^a * (L/N)^(1-a) := by
  rw [Real.div_rpow hL.le hN.le]
  have he : N^a / N = 1 / N^(1-a) := by
    have h : N^a / N = N^(a-1) := by rw [Real.rpow_sub hN, Real.rpow_one]
    rw [h]
    rw [show a-1 = -(1-a) by ring, Real.rpow_neg hN.le, one_div]
  calc
    (u^a * L^(1-a)) * (N^a / a) / N =
      (1/a) * u^a * L^(1-a) * (N^a / N) := by ring
    _ = (1/a) * u^a * (L^(1-a) / N^(1-a)) := by rw [he]; ring

theorem sampleThreshold_bias_average (ε u : ℝ) (hε : 0 ≤ ε) (hu : 0 < u)
    (t n : ℕ) (hn : 0 < n) :
    (∑ s ∈ Finset.range n, u / (sampleThreshold ε u t s)^ε) / n ≤
      (1+ε) * u^(1/(1+ε)) * (confidenceLog t / n)^(ε/(1+ε)) := by
  have hp : 0 < 1+ε := by linarith
  have hL : 0 < confidenceLog t := by
    unfold confidenceLog
    exact mul_pos (by norm_num) (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  have he : (1/(1+ε))*ε = 1-1/(1+ε) := by field_simp; ring
  have hq : 1-1/(1+ε) = ε/(1+ε) := by field_simp; ring
  have h := div_le_div_of_nonneg_right (sampleThreshold_bias_sum ε u hε hu t n)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [power_scale_bias u (confidenceLog t) (1/(1+ε)) ε hu hL he,
    power_bias_normalization u (confidenceLog t) (1/(1+ε)) n hL (Nat.cast_pos.mpr hn),
    one_div_one_div, hq] at h
  exact h

theorem threshold_scale_identity (u L N a : ℝ) (hu : 0 ≤ u) (hL : 0 < L) (hN : 0 < N) :
    (u*N/L)^a * L = N * (u^a * (L/N)^(1-a)) := by
  rw [Real.div_rpow (mul_nonneg hu hN.le) hL.le,
    Real.mul_rpow hu hN.le, Real.div_rpow hL.le hN.le]
  have hl : L / L^a = L^(1-a) := by rw [Real.rpow_sub hL, Real.rpow_one]
  have hn : N / N^(1-a) = N^a := by
    calc
      N / N^(1-a) = N^(1-(1-a)) := by
        simpa only [Real.rpow_one] using (Real.rpow_sub hN (1 : ℝ) (1-a)).symm
      _ = N^a := by congr 1; ring
  calc
    (u^a * N^a / L^a) * L = u^a * N^a * (L / L^a) := by ring
    _ = u^a * (N / N^(1-a)) * L^(1-a) := by rw [hl, hn]
    _ = N * (u^a * (L^(1-a) / N^(1-a))) := by ring

theorem threshold_variance_identity (u L N ε : ℝ) (hu : 0 < u) (hL : 0 < L)
    (hN : 0 < N) (hp : 0 < 1+ε) :
    N*u*((u*N/L)^(1/(1+ε)))^(1-ε)*L = ((u*N/L)^(1/(1+ε))*L)^2 := by
  let B := (u*N/L)^(1/(1+ε))
  have hB : 0 < B := Real.rpow_pos_of_pos (div_pos (mul_pos hu hN) hL) _
  have hb : B^(1+ε) = u*N/L := by
    dsimp [B]
    simpa only [one_div] using Real.rpow_inv_rpow (div_pos (mul_pos hu hN) hL).le hp.ne'
  have hm : B^(1+ε)*B^(1-ε) = B^2 := by
    rw [← Real.rpow_add hB, show (1+ε)+(1-ε) = (2 : ℝ) by ring, Real.rpow_two]
  have hb' : N*u = B^(1+ε)*L := by rw [hb]; field_simp
  change N*u*B^(1-ε)*L = (B*L)^2
  rw [hb']
  calc
    B^(1+ε)*L*B^(1-ε)*L = (B^(1+ε)*B^(1-ε))*L^2 := by ring
    _ = (B*L)^2 := by rw [hm]; ring

theorem confidenceLog_pos (t : ℕ) : 0 < confidenceLog t := by
  exact mul_pos (by norm_num) (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))

theorem sampleThreshold_pos (ε u : ℝ) (hu : 0 < u) (t s : ℕ) :
    0 < sampleThreshold ε u t s :=
  Real.rpow_pos_of_pos (div_pos (mul_pos hu (by positivity)) (confidenceLog_pos t)) _

theorem sampleThreshold_le_terminal (ε u : ℝ) (hε : 0 ≤ ε) (hu : 0 ≤ u)
    (t n s : ℕ) (hs : s < n) :
    sampleThreshold ε u t s ≤ (u*n/confidenceLog t)^(1/(1+ε)) := by
  apply Real.rpow_le_rpow (div_nonneg (mul_nonneg hu (by positivity)) (confidenceLog_pos t).le)
  · apply div_le_div_of_nonneg_right _ (confidenceLog_pos t).le
    apply mul_le_mul_of_nonneg_left _ hu
    exact_mod_cast hs
  · positivity

theorem sampleThreshold_variance_sum (ε u : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hu : 0 < u) (t n : ℕ) :
    (∑ s ∈ Finset.range n, u * (sampleThreshold ε u t s)^(1-ε)) ≤
      n*u*((u*n/confidenceLog t)^(1/(1+ε)))^(1-ε) := by
  calc
    _ ≤ ∑ _s ∈ Finset.range n, u * ((u*n/confidenceLog t)^(1/(1+ε)))^(1-ε) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sampleThreshold_pos ε u hu t s).le
          (sampleThreshold_le_terminal ε u hε0 hu.le t n s (Finset.mem_range.mp hs))
          (sub_nonneg.mpr hε)) hu.le
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem tuned_radius_le (ε u : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u)
    (t n : ℕ) (hn : 0 < n) :
    ((∑ s ∈ Finset.range n, u / (sampleThreshold ε u t s)^ε) +
      (2 * Real.sqrt ((∑ s ∈ Finset.range n, u * (sampleThreshold ε u t s)^(1-ε)) *
        confidenceLog t) + 2 * (u*n/confidenceLog t)^(1/(1+ε)) * confidenceLog t)) / n ≤
      confidenceRadius ε u t n := by
  let L := confidenceLog t
  let B := (u*n/L)^(1/(1+ε))
  let R := u^(1/(1+ε)) * (L/n)^(ε/(1+ε))
  have hL : 0 < L := confidenceLog_pos t
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < 1+ε := by linarith
  have hB : 0 < B := Real.rpow_pos_of_pos (div_pos (mul_pos hu hN) hL) _
  have hR : 0 ≤ R := mul_nonneg (Real.rpow_nonneg hu.le _)
    (Real.rpow_nonneg (div_pos hL hN).le _)
  have hq : 1-1/(1+ε) = ε/(1+ε) := by field_simp; ring
  have hBL : B*L = n*R := by
    dsimp [B, R]
    rw [threshold_scale_identity u L n (1/(1+ε)) hu.le hL hN, hq]
  have hBdiv : B*L/n = R := (div_eq_iff hN.ne').mpr (by rw [hBL]; ring)
  have hv := mul_le_mul_of_nonneg_right
    (sampleThreshold_variance_sum ε u hε0 hε hu t n) hL.le
  have hs : Real.sqrt ((∑ s ∈ Finset.range n,
      u * (sampleThreshold ε u t s)^(1-ε))*L) ≤ B*L := by
    apply (Real.sqrt_le_left (mul_pos hB hL).le).mpr
    exact hv.trans_eq (threshold_variance_identity u L n ε hu hL hN hp)
  have hsdiv := (div_le_div_of_nonneg_right hs hN.le).trans_eq hBdiv
  have hbias := sampleThreshold_bias_average ε u hε0 hu t n hn
  change _ ≤ (1+ε)*u^(1/(1+ε))*(L/n)^(ε/(1+ε)) at hbias
  change _ ≤ 8*u^(1/(1+ε))*(L/n)^(ε/(1+ε))
  have hrhs : 8*u^(1/(1+ε))*(L/n)^(ε/(1+ε)) = 8*R := by dsimp [R]; ring
  rw [hrhs]
  change ((∑ s ∈ Finset.range n, u / (sampleThreshold ε u t s)^ε) +
    (2 * Real.sqrt ((∑ s ∈ Finset.range n, u * (sampleThreshold ε u t s)^(1-ε))*L) +
      2*B*L)) / n ≤ 8*R
  have hbias' : (∑ s ∈ Finset.range n, u / (sampleThreshold ε u t s)^ε) / n ≤
      (1+ε)*R := by simpa only [R, mul_assoc] using hbias
  calc
    _ = (∑ s ∈ Finset.range n, u / (sampleThreshold ε u t s)^ε) / n +
      2*(Real.sqrt ((∑ s ∈ Finset.range n, u * (sampleThreshold ε u t s)^(1-ε))*L)/n) +
      2*(B*L/n) := by ring
    _ ≤ 8*R := by rw [hBdiv]; nlinarith [mul_nonneg (sub_nonneg.mpr hε) hR]

end BanditRLProof.HeavyTail
