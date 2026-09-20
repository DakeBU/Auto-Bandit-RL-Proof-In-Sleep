import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import BanditRLProof.Algorithms.MusicalChairsExploration

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def rewardLaw {k : ℕ} (nu : Fin k → Measure ℝ) (T : ℕ) :
    Measure (Fin T → Fin k → ℝ) := Measure.pi (fun _ : Fin T => Measure.pi nu)

instance rewardLaw_probability {k : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (T : ℕ) : IsProbabilityMeasure (rewardLaw nu T) := by
  unfold rewardLaw
  infer_instance

noncomputable def armMean {k : ℕ} (nu : Fin k → Measure ℝ) (a : Fin k) : ℝ :=
  ∫ y, y ∂nu a

theorem reward_coordinate_preserving {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (t : Fin T) (a : Fin k) :
    MeasurePreserving (fun r : Fin T → Fin k → ℝ => r t a) (rewardLaw nu T) (nu a) := by
  exact (measurePreserving_eval nu a).comp
    (measurePreserving_eval (fun _ : Fin T => Measure.pi nu) t)

theorem reward_coordinate_mean {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (t : Fin T) (a : Fin k) :
    (∫ r, r t a ∂rewardLaw nu T) = armMean nu a := by
  have hm := reward_coordinate_preserving nu t a
  calc
    _ = ∫ y, y ∂(rewardLaw nu T).map (fun r => r t a) :=
      (integral_map hm.measurable.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = _ := by rw [hm.map_eq]; rfl

theorem reward_coordinate_bounded {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) (a : Fin k) :
    ∀ᵐ r ∂rewardLaw nu T, r t a ∈ Set.Icc (0 : ℝ) 1 :=
  (reward_coordinate_preserving nu t a).quasiMeasurePreserving.ae (hb a)

theorem reward_coordinate_subGaussian {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) (a : Fin k) :
    HasSubgaussianMGF (fun r : Fin T → Fin k → ℝ => r t a - armMean nu a)
      (1/4 : NNReal) (rewardLaw nu T) := by
  have h := hasSubgaussianMGF_of_mem_Icc
    (reward_coordinate_preserving nu t a).measurable.aemeasurable
    (reward_coordinate_bounded nu hb t a)
  norm_num [reward_coordinate_mean] at h ⊢
  exact h

theorem reward_time_independent {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (a : Fin k) :
    iIndepFun (fun t (r : Fin T → Fin k → ℝ) => r t a - armMean nu a) (rewardLaw nu T) := by
  apply iIndepFun_pi (Ω := fun _ : Fin T => Fin k → ℝ) (𝓧 := fun _ : Fin T => ℝ)
    (μ := fun _ : Fin T => Measure.pi nu)
    (X := fun _ (r : Fin k → ℝ) => r a - armMean nu a)
  intro t
  exact (show Measurable (fun r : Fin k → ℝ => r a - armMean nu a) from
    (measurable_pi_apply a).sub measurable_const).aemeasurable

theorem selected_sum_subGaussian {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k) :
    HasSubgaussianMGF (fun r : Fin T → Fin k → ℝ => ∑ t ∈ S, (r t a - armMean nu a))
      ((S.card : NNReal)/4) (rewardLaw nu T) := by
  have h := HasSubgaussianMGF.sum_of_iIndepFun (reward_time_independent nu a)
    (fun t (_ : t ∈ S) => reward_coordinate_subGaussian nu hb t a)
  simpa [div_eq_mul_inv] using h


theorem selected_sum_abs_tail {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (u : ℝ) (hu : 0 ≤ u) :
    (rewardLaw nu T).real {r | u ≤ |∑ t ∈ S, (r t a - armMean nu a)|} ≤
      2 * Real.exp (-u^2 / (2 * ((S.card : ℝ)/4))) := by
  have h := selected_sum_subGaussian nu hb S a
  have hp := h.measure_ge_le hu
  have hn := h.neg.measure_ge_le hu
  have he : {r : Fin T → Fin k → ℝ | u ≤ |∑ t ∈ S, (r t a - armMean nu a)|} =
      {r | u ≤ ∑ t ∈ S, (r t a - armMean nu a)} ∪
      {r | u ≤ -(∑ t ∈ S, (r t a - armMean nu a))} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [he]
  have hU := measureReal_union_le (μ := rewardLaw nu T)
    {r | u ≤ ∑ t ∈ S, (r t a - armMean nu a)}
    {r | u ≤ -(∑ t ∈ S, (r t a - armMean nu a))}
  simp only [Pi.neg_apply, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] at hp hn
  linarith

noncomputable def selectedMean {k T : ℕ} (S : Finset (Fin T)) (a : Fin k)
    (r : Fin T → Fin k → ℝ) : ℝ :=
  if S.card = 0 then 0 else (∑ t ∈ S, r t a) / S.card

theorem selected_centered_sum {k T : ℕ} (nu : Fin k → Measure ℝ)
    (S : Finset (Fin T)) (a : Fin k) (hS : 0 < S.card) (r : Fin T → Fin k → ℝ) :
    (∑ t ∈ S, (r t a - armMean nu a)) = (S.card : ℝ) * (selectedMean S a r - armMean nu a) := by
  have h0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  simp only [selectedMean, if_neg (Nat.ne_of_gt hS), Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem selectedMean_tail_pos {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (hS : 0 < S.card) (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤
      2 * Real.exp (-(S.card : ℝ) * eps^2 / 2) := by
  have hD : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have he : {r : Fin T → Fin k → ℝ | eps/2 ≤ |selectedMean S a r - armMean nu a|} =
      {r | (S.card : ℝ) * eps/2 ≤ |∑ t ∈ S, (r t a - armMean nu a)|} := by
    ext r
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, selected_centered_sum nu S a hS r,
      abs_mul, abs_of_pos hD]
    rw [mul_div_assoc, mul_le_mul_iff_right₀ hD]
  rw [he]
  have h := selected_sum_abs_tail nu hb S a ((S.card : ℝ)*eps/2) (by positivity)
  convert h using 1
  congr 2
  field_simp
  ring


theorem selectedMean_tail {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤
      2 * Real.exp (-(S.card : ℝ) * eps^2 / 2) := by
  by_cases hS : S.card = 0
  · have h : (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤ 1 :=
      measureReal_le_one
    simpa [hS] using h.trans (by norm_num : (1 : ℝ) ≤ 2)
  · exact selectedMean_tail_pos nu hb S a (Nat.pos_of_ne_zero hS) eps heps

noncomputable def observedTimes {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (i : Fin n) (a : Fin k) : Finset (Fin T) :=
  Finset.univ.filter (fun t => x t ∈ observes i a)

theorem localEmpiricalMean_eq_selectedMean {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (r : Fin T → Fin k → ℝ) (i : Fin n) (a : Fin k) :
    localEmpiricalMean (explorationFeedback x r i) a = selectedMean (observedTimes x i a) a r := by
  simp only [localEmpiricalMean, localObservationCount_eq, localRewardSum_eq,
    selectedMean, observedTimes, observationCount, FinitePMF.eventCount]

theorem localEmpiricalMean_fixed_tail {n k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin T → Fin n → Fin k) (i : Fin n) (a : Fin k) (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |localEmpiricalMean (explorationFeedback x r i) a - armMean nu a|} ≤
      2 * Real.exp (-(observationCount i a x : ℝ) * eps^2 / 2) := by
  simp_rw [localEmpiricalMean_eq_selectedMean]
  exact selectedMean_tail nu hb (observedTimes x i a) a eps heps

theorem measurable_selectedMean {k T : ℕ} (S : Finset (Fin T)) (a : Fin k) :
    Measurable (selectedMean S a) := by
  unfold selectedMean
  split_ifs <;> fun_prop

theorem measurable_jointEmpiricalMean {n k T : ℕ} (i : Fin n) (a : Fin k) :
    Measurable (fun z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ) =>
      localEmpiricalMean (explorationFeedback z.1 z.2 i) a) := by
  apply measurable_from_prod_countable_right
  intro x
  simp_rw [localEmpiricalMean_eq_selectedMean]
  exact measurable_selectedMean (observedTimes x i a) a

noncomputable def explorationRewardLaw {n k T : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) :
    Measure ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  (explorationLaw n k T hk).toMeasure.prod (rewardLaw nu T)

instance explorationRewardLaw_probability {n k T : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    IsProbabilityMeasure (explorationRewardLaw (n := n) (T := T) hk nu) := by
  unfold explorationRewardLaw
  infer_instance

def meanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ) (i : Fin n) (a : Fin k) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | eps/2 ≤ |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a|}

theorem measurableSet_meanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ)
    (i : Fin n) (a : Fin k) (eps : ℝ) : MeasurableSet (meanBadEvent (T := T) nu i a eps) := by
  exact measurableSet_le measurable_const ((measurable_jointEmpiricalMean i a).sub_const (armMean nu a)).abs

theorem meanBadEvent_mixture {n k T : ℕ} (hk : 0 < k) (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (i : Fin n) (a : Fin k) (eps : ℝ) :
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) =
      ∑ x, explorationLaw n k T hk x *
        rewardLaw nu T {r | eps/2 ≤ |localEmpiricalMean (explorationFeedback x r i) a - armMean nu a|} := by
  rw [explorationRewardLaw, Measure.prod_apply (measurableSet_meanBadEvent nu i a eps), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), mul_comm]
  rfl


theorem meanBadEvent_count_bound {n k T : ℕ} (hk : 0 < k) (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (a : Fin k) (eps : ℝ) (heps : 0 ≤ eps) :
    let q := (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) ≤
      2 * (q * ENNReal.ofReal (Real.exp (-(eps^2/2))) + (1-q))^T := by
  dsimp
  rw [meanBadEvent_mixture]
  calc
    _ ≤ ∑ x, explorationLaw n k T hk x * ENNReal.ofReal
        (2 * Real.exp (-(observationCount i a x : ℝ) * eps^2 / 2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_right
      rw [← ofReal_measureReal (μ := rewardLaw nu T)]
      exact ENNReal.ofReal_le_ofReal (localEmpiricalMean_fixed_tail nu hb x i a eps heps)
    _ = 2 * (∑ x, explorationLaw n k T hk x * ENNReal.ofReal
        (Real.exp (-(eps^2/2) * (observationCount i a x : ℝ)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have he : -(observationCount i a x : ℝ) * eps^2 / 2 =
          -(eps^2/2) * (observationCount i a x : ℝ) := by ring
      rw [he, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ = _ := by rw [observationCount_laplace]


theorem half_le_one_sub_exp_neg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x/2 ≤ 1 - Real.exp (-x) := by
  have hprod : (1+x) * Real.exp (-x) ≤ 1 := by
    calc
      _ ≤ Real.exp x * Real.exp (-x) := by
        gcongr
        linarith [Real.add_one_le_exp x]
      _ = 1 := by rw [← Real.exp_add]; simp
  have hquad : 0 ≤ x * (1-x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  by_contra hh
  have hlt : (1-x/2)*(1+x) < Real.exp (-x)*(1+x) := by
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  nlinarith

theorem count_mixture_exp_bound (q eps : ℝ) (T : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    (q * Real.exp (-(eps^2/2)) + (1-q))^T ≤
      Real.exp (-(T : ℝ)*q*eps^2/4) := by
  have hsmall := half_le_one_sub_exp_neg (eps^2/2) (by positivity) (by nlinarith)
  have hbase : q * Real.exp (-(eps^2/2)) + (1-q) ≤
      Real.exp (-q*(1-Real.exp (-(eps^2/2)))) := by
    have h := Real.add_one_le_exp (-q*(1-Real.exp (-(eps^2/2))))
    nlinarith
  calc
    _ ≤ (Real.exp (-q*(1-Real.exp (-(eps^2/2)))))^T := by
      gcongr
      exact add_nonneg (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1)
    _ = Real.exp ((T : ℝ) * (-q*(1-Real.exp (-(eps^2/2))))) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (Nat.cast_nonneg T) hq0)
      nlinarith


noncomputable def explorationProbReal (n k : ℕ) : ℝ :=
  (1 / (k : ℝ)) * (((k-1 : ℕ) : ℝ) / (k : ℝ))^(n-1)

theorem explorationProbReal_nonneg (n k : ℕ) : 0 ≤ explorationProbReal n k := by
  unfold explorationProbReal
  positivity

theorem explorationProbReal_le_one (n k : ℕ) (hk : 0 < k) : explorationProbReal n k ≤ 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hb : (((k-1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.sub_le k 1)
  have hp : ((((k-1 : ℕ) : ℝ) / (k : ℝ))^(n-1)) ≤ 1 := by
    calc
      _ ≤ (1 : ℝ)^(n-1) := by gcongr
      _ = 1 := one_pow _
  have hdiv : (1 : ℝ)/k ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.succ_le_iff.mpr hk)
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans (by simpa using hdiv)

theorem explorationProbReal_lower (n k : ℕ) (hk : 0 < k) (hnk : n ≤ k) :
    (1 : ℝ)/(4*k) ≤ explorationProbReal n k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hb : (((k-1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.sub_le k 1)
  calc
    _ ≤ (1/(k : ℝ)) * (((k-1 : ℕ) : ℝ)/(k : ℝ))^(k-1) := real_uniform_hazard_lower k hk
    _ ≤ explorationProbReal n k := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by positivity) hb (Nat.sub_le_sub_right hnk 1)) (by positivity)

theorem ofReal_explorationProbReal (n k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (explorationProbReal n k) =
      (1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1) := by
  unfold explorationProbReal
  simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/k),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < k), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ((k-1 : ℕ) : ℝ)/(k : ℝ))]

theorem meanBadEvent_exponential_bound {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (a : Fin k) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) ≤
      ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*eps^2/(16*k))) := by
  let q := explorationProbReal n k
  have hq0 : 0 ≤ q := explorationProbReal_nonneg n k
  have hq1 : q ≤ 1 := explorationProbReal_le_one n k hk
  have hbase : 0 ≤ q * Real.exp (-(eps^2/2)) + (1-q) :=
    add_nonneg (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1)
  have hconv : 2 * (((1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1)) *
      ENNReal.ofReal (Real.exp (-(eps^2/2))) +
      (1-((1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1))))^T =
      ENNReal.ofReal (2 * (q * Real.exp (-(eps^2/2)) + (1-q))^T) := by
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hbase,
      ENNReal.ofReal_add (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1),
      ENNReal.ofReal_mul hq0, ENNReal.ofReal_sub 1 hq0, ENNReal.ofReal_one,
      q, ofReal_explorationProbReal n k hk]
  calc
    _ ≤ _ := meanBadEvent_count_bound hk nu hb i a eps heps0
    _ = _ := hconv
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*q*eps^2/4)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (count_mixture_exp_bound q eps T hq0 hq1 heps0 heps1) (by norm_num)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left (explorationProbReal_lower n k hk hnk)
        (by positivity : 0 ≤ (T : ℝ)*eps^2/4)
      calc
        _ = -((T : ℝ)*eps^2/4*q) := by ring
        _ ≤ -((T : ℝ)*eps^2/4*(1/(4*k))) := neg_le_neg hmul
        _ = _ := by ring


def allMeanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  ⋃ i : Fin n, ⋃ a : Fin k, meanBadEvent nu i a eps

theorem allMeanBadEvent_exponential_bound {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw hk nu (allMeanBadEvent (n := n) (T := T) nu eps) ≤
      ENNReal.ofReal (2 * (k : ℝ)^2 * Real.exp (-(T : ℝ)*eps^2/(16*k))) := by
  let M := explorationRewardLaw (n := n) (T := T) hk nu
  let B := ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*eps^2/(16*k)))
  have hnkE : (n : ℝ≥0∞) ≤ k := by exact_mod_cast hnk
  calc
    _ ≤ ∑ i : Fin n, M (⋃ a : Fin k, meanBadEvent nu i a eps) := by
      simpa only [tsum_fintype] using (measure_iUnion_le (μ := M)
        (fun i : Fin n => ⋃ a : Fin k, meanBadEvent nu i a eps))
    _ ≤ ∑ i : Fin n, ∑ a : Fin k, M (meanBadEvent nu i a eps) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [tsum_fintype] using (measure_iUnion_le (μ := M) (fun a : Fin k => meanBadEvent nu i a eps))
    _ ≤ ∑ _i : Fin n, ∑ _a : Fin k, B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro a _
      exact meanBadEvent_exponential_bound hk hnk nu hb i a eps heps0 heps1
    _ = (n : ℝ≥0∞) * (k : ℝ≥0∞) * B := by simp [mul_assoc]
    _ ≤ (k : ℝ≥0∞) * (k : ℝ≥0∞) * B := by gcongr
    _ = _ := by
      simp only [B, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2*(k : ℝ)^2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      ring

theorem mean_exploration_threshold (k T : ℕ) (hk : 0 < k) (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    2*(k : ℝ)^2 * Real.exp (-(T : ℝ)*eps^2/(16*k)) ≤ delta/2 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log (4*(k : ℝ)^2/delta) ≤ (T : ℝ)*eps^2/(16*k) := by
    have hmul := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ eps^2/(16*(k : ℝ)))
    have he : ((16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta)) * (eps^2/(16*(k : ℝ))) =
        Real.log (4*(k : ℝ)^2/delta) := by field_simp
    rw [he] at hmul
    simpa only [mul_div_assoc] using hmul
  calc
    _ ≤ 2*(k : ℝ)^2 * Real.exp (-Real.log (4*(k : ℝ)^2/delta)) := by
      gcongr
      convert neg_le_neg hlog using 1
      ring
    _ = delta/2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      ring

theorem allMeanBadEvent_le_half_delta {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    explorationRewardLaw hk nu (allMeanBadEvent (n := n) (T := T) nu eps) ≤
      ENNReal.ofReal (delta/2) := by
  exact (allMeanBadEvent_exponential_bound hk hnk nu hb eps heps.le heps1).trans
    (ENNReal.ofReal_le_ofReal (mean_exploration_threshold k T hk eps delta heps hdelta hT))



def allMeanAccurate {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | ∀ i : Fin n, ∀ a : Fin k,
    |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a| < eps/2}

theorem allMeanAccurate_eq_compl {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    allMeanAccurate (n := n) (T := T) nu eps = (allMeanBadEvent nu eps)ᶜ := by
  ext z
  simp [allMeanAccurate, allMeanBadEvent, meanBadEvent]

theorem allMeanAccurate_probability {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    1 - ENNReal.ofReal (delta/2) ≤
      explorationRewardLaw hk nu (allMeanAccurate (n := n) (T := T) nu eps) := by
  have hm : MeasurableSet (allMeanBadEvent (n := n) (T := T) nu eps) :=
    MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun a => measurableSet_meanBadEvent nu i a eps))
  rw [allMeanAccurate_eq_compl, measure_compl hm (by finiteness), measure_univ]
  exact tsub_le_tsub_left (allMeanBadEvent_le_half_delta hk hnk nu hb eps delta heps heps1 hdelta hT) 1


end BanditRLProof.MusicalChairs
