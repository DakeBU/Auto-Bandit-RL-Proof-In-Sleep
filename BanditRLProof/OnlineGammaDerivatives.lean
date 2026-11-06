import BanditRLProof.OnlineGammaEstimates

/-! # Derivatives of the real log Gamma function

Euler approximants converge uniformly on bounded open intervals with positive
left endpoint. Their limits identify both derivatives on the positive half-line.
-/

namespace BanditRL.OnlineGamma

open Filter Finset Set

noncomputable def logGammaSlope (y : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant - 1 / y +
    ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / (y + ((k : ℝ) + 1)))

noncomputable def logGammaCurvature (y : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / (y + (k : ℝ)) ^ 2
private theorem harmonic_real_range (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ range n, (1 : ℝ) / ((k : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [harmonic_succ, Rat.cast_add, ih, sum_range_succ]; simp

private theorem first_split (n : ℕ) (y : ℝ) :
    logGammaSlopeApprox n y = Real.log (n : ℝ) - (harmonic n : ℝ) - 1/y +
      ∑ k ∈ range n, compensatedReciprocal k y := by
  rw [logGammaSlopeApprox, Finset.sum_range_succ', harmonic_real_range]
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, compensatedReciprocal, sum_sub_distrib]
  ring

private theorem second_split (n : ℕ) (y : ℝ) :
    logGammaCurvatureApprox n y = 1/y^2 + ∑ k ∈ range n, shiftedInvSq k y := by
  rw [logGammaCurvatureApprox, Finset.sum_range_succ']
  simp [shiftedInvSq, add_comm]

private theorem positive_second_series (y : ℝ) (hy : 0 < y) :
    Summable (fun k : ℕ => (1 : ℝ) / (y + (k : ℝ))^2) := by
  apply (summable_nat_add_iff (f := fun k : ℕ => (1 : ℝ) / (y + (k : ℝ))^2) 1).1
  have hh := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) 1).2
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  refine hh.of_nonneg_of_le (fun _ => by positivity) ?_
  intro k
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  exact one_div_le_one_div_of_le (sq_pos_of_pos hk)
    (by nlinarith [mul_nonneg hy.le hk.le, sq_nonneg y])

private theorem constant_in_index (f : ℝ → ℝ) (S : Set ℝ) :
    TendstoUniformlyOn (fun (_ : ℕ) => f) f atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε

theorem tendstoUniformlyOn_logGammaSlopeApprox_and_curvatureApprox (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    TendstoUniformlyOn logGammaSlopeApprox logGammaSlope Filter.atTop (Set.Ioo a b) ∧
    TendstoUniformlyOn logGammaCurvatureApprox logGammaCurvature Filter.atTop (Set.Ioo a b) := by
  obtain ⟨ht, hq⟩ := tendstoUniformlyOn_compensatedReciprocal_and_shiftedInvSq a b ha hab
  have sub : Ioo a b ⊆ Icc a b := fun _ h => ⟨h.1.le, h.2.le⟩
  have hc : Tendsto (fun n : ℕ => Real.log (n : ℝ) - (harmonic n : ℝ))
      atTop (nhds (-Real.eulerMascheroniConstant)) := by
    simpa only [neg_sub] using Real.tendsto_harmonic_sub_log.neg
  constructor
  · have h := ((hc.tendstoUniformlyOn_const (Ioo a b)).sub
        (constant_in_index (fun y => 1/y) (Ioo a b))).add (ht.mono sub)
    apply h.congr
    exact Filter.Eventually.of_forall fun n y _ => (first_split n y).symm
  · have h := (constant_in_index (fun y => 1/y^2) (Ioo a b)).add (hq.mono sub)
    apply (h.congr_right ?_).congr
    · exact Filter.Eventually.of_forall fun n y _ => (second_split n y).symm
    · intro y hy
      have hs := (positive_second_series y (ha.trans hy.1)).tsum_eq_zero_add
      simpa [logGammaCurvature, shiftedInvSq, Nat.cast_add, Nat.cast_one] using hs.symm

private theorem logGamma_first_limit (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => Real.log (Real.Gamma z)) (logGammaSlope y) y := by
  have ha : 0 < y / 2 := by positivity
  have hab : y / 2 < 2 * y := by linarith
  have hyS : y ∈ Set.Ioo (y / 2) (2 * y) := ⟨by linarith, by linarith⟩
  apply hasDerivAt_of_tendstoUniformlyOn (f := fun n z => Real.BohrMollerup.logGammaSeq z n)
    isOpen_Ioo (tendstoUniformlyOn_logGammaSlopeApprox_and_curvatureApprox _ _ ha hab).1 _ _ hyS
  · exact Filter.Eventually.of_forall fun n z hz => (hasDerivAt_logGammaSeq_and_slopeApprox n z (ha.trans hz.1)).1
  · exact fun z hz => Real.BohrMollerup.tendsto_log_gamma (ha.trans hz.1)

theorem logGamma_derivatives (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => Real.log (Real.Gamma z)) (logGammaSlope y) y ∧
    HasDerivAt (deriv (fun z : ℝ => Real.log (Real.Gamma z))) (logGammaCurvature y) y ∧
    HasSum (fun k : ℕ => 1 / (y + (k : ℝ)) ^ 2) (logGammaCurvature y) := by
  have ha : 0 < y / 2 := by positivity
  have hab : y / 2 < 2 * y := by linarith
  have hyS : y ∈ Set.Ioo (y / 2) (2 * y) := ⟨by linarith, by linarith⟩
  obtain ⟨hfirst, hsecond⟩ := tendstoUniformlyOn_logGammaSlopeApprox_and_curvatureApprox _ _ ha hab
  have hd : HasDerivAt logGammaSlope (logGammaCurvature y) y :=
    hasDerivAt_of_tendstoUniformlyOn (f := logGammaSlopeApprox) isOpen_Ioo hsecond
      (Filter.Eventually.of_forall fun n z hz => (hasDerivAt_logGammaSeq_and_slopeApprox n z (ha.trans hz.1)).2)
      (fun z hz => hfirst.tendsto_at hz) hyS
  refine ⟨logGamma_first_limit y hy, hd.congr_of_eventuallyEq ?_, (positive_second_series y hy).hasSum⟩
  filter_upwards [lt_mem_nhds hy] with z hz
  exact (logGamma_first_limit z hz).deriv

end BanditRL.OnlineGamma
