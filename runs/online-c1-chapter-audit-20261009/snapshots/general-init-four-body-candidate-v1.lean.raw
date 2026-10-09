import BanditRLProof.OnlineLearningFTLState
import BanditRLProof.OnlineFTLLimitSemantics

open Filter

namespace BanditRL.OnlineLearning

/-- Derived same-run identity: only the scored initial loss differs from half initialization. -/
theorem ftlPredict_bestRegret_initial_correction (initial : ℝ) (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T) :
    squaredBestRegret y (ftlPredict initial y) T =
      squaredBestRegret y (meanPredict y) T +
        ((initial - y 0)^2 - ((1 : ℝ) / 2 - y 0)^2) := by
  cases T with
  | zero => omega
  | succ n =>
    have htail :
        (∑ t ∈ Finset.range n, (ftlPredict initial y (t + 1) - y (t + 1))^2) =
          ∑ t ∈ Finset.range n, (meanPredict y (t + 1) - y (t + 1))^2 := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [ftlPredict, meanPredict]
    have hsum :
        (∑ t ∈ Finset.range (n + 1), (ftlPredict initial y t - y t)^2) =
          (∑ t ∈ Finset.range (n + 1), (meanPredict y t - y t)^2) +
            ((initial - y 0)^2 - ((1 : ℝ) / 2 - y 0)^2) := by
      simp only [Finset.sum_range_succ']
      rw [htail]
      simp [ftlPredict, meanPredict]
    unfold squaredBestRegret
    rw [hsum]
    ring

/-- Derived general-initialization guarantee; the half-initial quarter is not universal. -/
theorem ftlPredict_bestRegret_refined (initial : ℝ) (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y (ftlPredict initial y) T ≤
      (1 : ℝ) + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2) := by
  have hz := hy 0 hT
  have haa : initial ^ 2 ≤ initial := by
    nlinarith [mul_nonneg hi.1 (sub_nonneg.mpr hi.2)]
  have hfirst : (1 : ℝ) / 4 +
      ((initial - y 0)^2 - ((1 : ℝ) / 2 - y 0)^2) ≤ 1 := by
    by_cases hsmall : y 0 ≤ (1 : ℝ) / 2
    · nlinarith [mul_nonneg (sub_nonneg.mpr hi.2)
        (show 0 ≤ 1 - 2 * y 0 by linarith), hz.1]
    · nlinarith [mul_nonneg hi.1
        (show 0 ≤ 2 * y 0 - 1 by linarith), hz.2]
  rw [ftlPredict_bestRegret_initial_correction initial y T hT]
  have hhalf := meanPredict_bestRegret_refined y T hT hy
  linarith

/-- Actual general-initial FTL has comparator-wise eventual upper regret, without ordinary limits. -/
theorem ftlPredict_upperNoRegret (initial : ℝ) (y : ℕ → ℝ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) :
    NoRegret (Set.Icc (0 : ℝ) 1)
      (fun t x => (x - y t)^2) (ftlPredict initial y) := by
  apply noRegret_of_vanishing_bound _ _ _ (fun _ T => (5 + 4 * Real.log T) / T)
  · intro u hu
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
    have hcmp := comparatorRegret_le_squaredBestRegret y (ftlPredict initial y) T
      (fun t _ => hy t) u hu
    have hhalf := meanPredict_bestRegret_bound y T hT (fun t _ => hy t)
    have heq := ftlPredict_bestRegret_initial_correction initial y T hT
    have hfirst : (initial - y 0)^2 ≤ 1 := by
      nlinarith [mul_nonneg
        (show 0 ≤ 1 - (initial - y 0) by linarith [(hy 0).1, hi.2])
        (show 0 ≤ 1 + (initial - y 0) by linarith [hi.1, (hy 0).2])]
    linarith [sq_nonneg ((1 : ℝ) / 2 - y 0)]
  · intro u hu
    have h0 : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hc : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hh := ((h0.comp hc).const_mul 5).add ((h1.comp hc).const_mul 4)
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    ext T
    dsimp [Function.comp_def]
    ring

/-- The actual initialized predictor has ordinary zero average TRUE-best regret. -/
theorem ftlPredict_bestRegret_average_tendsto_zero (initial : ℝ) (y : ℕ → ℝ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun T : ℕ =>
      squaredBestRegret y (ftlPredict initial y) T / (T : ℝ))
        atTop (nhds (0 : ℝ)) := by
  let correction : ℝ := (initial - y 0)^2 - ((1 : ℝ) / 2 - y 0)^2
  have hhalf := meanPredict_bestRegret_average_tendsto_zero y hy
  have hfirst := tendsto_const_div_atTop_nhds_zero_nat correction
  have hsum := hhalf.add hfirst
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
  rw [ftlPredict_bestRegret_initial_correction initial y T hT, add_div]

end BanditRL.OnlineLearning

/-!
Source: Orabona, arXiv:1912.13213v10 (21 June 2026), Chapter 1,
printed page 3 / PDF page 15: the strict-past mean strategy may start at
any point in [0,1] and has the stated winning guarantee. These four derived
interfaces keep that initialization fixed for one infinite run. Source round
1 is Lean index 0. The literal comparator infimum is the same at each scored
horizon; the finite terminal requires only that horizon's unit observations.

The unchanged printed Theorem 1.3 specifies initial 1/2. Its quarter-plus-tail
intermediate estimate remains separate from the general-initial 1-plus-tail
bound here. The private 5+4 log T estimate inside the upper-property proof is
only a derived analytic bound and does not replace either finite terminal.

The upper-epsilon comparator property and the ordinary zero limit of TRUE-best
average regret are distinct. These theorems assert no universal ordinary limit
for fixed-comparator regret. The bounded actual-half-FTL obstruction and the
pinned printed ordinary-limit definition in the shared library remain unchanged.
-/
