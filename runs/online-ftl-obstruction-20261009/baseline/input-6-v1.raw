import BanditRLProof.OnlineFTLLimitSemantics

open Filter
open BanditRL.OnlineLearning

namespace Tests.OnlineFTLLimitSemantics

def alternatingObservation (t : ℕ) : ℝ := if t % 2 = 0 then 0 else 1


theorem alternating_unit :
    (∀ t, alternatingObservation t ∈ Set.Icc (0 : ℝ) 1) ∧
    alternatingObservation 0 = 0 ∧ alternatingObservation 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    unfold alternatingObservation
    split_ifs <;> norm_num
  · norm_num [alternatingObservation]
  · norm_num [alternatingObservation]

theorem alternating_prefix_sum (T : ℕ) :
    (∑ t ∈ Finset.range T, alternatingObservation t) = ((T / 2 : ℕ) : ℝ) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : n % 2 = 0
    · have hdiv : (n + 1) / 2 = n / 2 := by omega
      simp [alternatingObservation, hn, hdiv]
    · have hdiv : (n + 1) / 2 = n / 2 + 1 := by omega
      simp [alternatingObservation, hn, hdiv, Nat.cast_add]

theorem alternating_mean_tendsto :
    Tendsto (empiricalMean alternatingObservation) atTop (nhds ((1 : ℝ) / 2)) := by
  have hbounds : ∀ᶠ T : ℕ in atTop,
      0 ≤ (1 : ℝ) / 2 - empiricalMean alternatingObservation T ∧
      (1 : ℝ) / 2 - empiricalMean alternatingObservation T ≤ 1 / (T : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    have hcount : ((T / 2 : ℕ) : ℝ) * 2 + ((T % 2 : ℕ) : ℝ) = (T : ℝ) := by
      exact_mod_cast (show T / 2 * 2 + T % 2 = T by omega)
    have hrem : (0 : ℝ) ≤ ((T % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrem1 : ((T % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast (show T % 2 ≤ 1 by omega)
    rw [empiricalMean, alternating_prefix_sum]
    constructor
    · apply sub_nonneg.mpr
      apply (div_le_iff₀ hTR).mpr
      nlinarith
    · apply (le_div_iff₀ hTR).mpr
      have hid : ((1 : ℝ) / 2 - ((T / 2 : ℕ) : ℝ) / (T : ℝ)) * (T : ℝ) =
          (T : ℝ) / 2 - ((T / 2 : ℕ) : ℝ) := by field_simp
      rw [hid]
      nlinarith
  have hinv : Tendsto (fun T : ℕ => (1 : ℝ) / (T : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hdiff : Tendsto (fun T : ℕ => (1 : ℝ) / 2 - empiricalMean alternatingObservation T)
      atTop (nhds 0) := squeeze_zero' (hbounds.mono (fun _ h => h.1))
        (hbounds.mono (fun _ h => h.2)) hinv
  have hres := (tendsto_const_nhds (x := (1 : ℝ) / 2)).sub hdiff
  simpa only [sub_zero, sub_sub_cancel] using hres

theorem alternating_initial_predictions :
    meanPredict alternatingObservation 0 = (1 : ℝ) / 2 ∧
    meanPredict alternatingObservation 1 = 0 ∧
    meanPredict alternatingObservation 2 = (1 : ℝ) / 2 ∧
    meanPredict alternatingObservation 3 = (1 : ℝ) / 3 := by
  norm_num [meanPredict, empiricalMean, alternatingObservation, Finset.sum_range_succ]

theorem alternating_best_regret_zero_one_two :
    squaredBestRegret alternatingObservation (meanPredict alternatingObservation) 0 = 0 ∧
    squaredBestRegret alternatingObservation (meanPredict alternatingObservation) 1 = (1 : ℝ) / 4 ∧
    squaredBestRegret alternatingObservation (meanPredict alternatingObservation) 2 = (3 : ℝ) / 4 := by
  have heq (T : ℕ) := squaredBestRegret_eq_comparatorRegret alternatingObservation
    (meanPredict alternatingObservation) T (fun t _ => alternating_unit.1 t)
  rw [heq 0, heq 1, heq 2]
  norm_num [comparatorRegret, meanPredict, empiricalMean, alternatingObservation, Finset.sum_range_succ]

theorem alternating_actual_gap_nonneg (T : ℕ) :
    0 ≤ comparatorRegret (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) (empiricalMean alternatingObservation T) T := by
  exact meanPredict_bestLoss_nonneg alternatingObservation T

theorem alternating_fixed_decomposition (u : ℝ) (T : ℕ) :
    comparatorRegret (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) u T =
    comparatorRegret (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) (empiricalMean alternatingObservation T) T -
      (T : ℝ) * (u - empiricalMean alternatingObservation T)^2 := by
  exact meanPredict_comparator_decomposition alternatingObservation u T

theorem alternating_best_average_zero :
    Tendsto (fun T : ℕ =>
      squaredBestRegret alternatingObservation (meanPredict alternatingObservation) T / (T : ℝ))
      atTop (nhds (0 : ℝ)) := by
  exact meanPredict_bestRegret_average_tendsto_zero alternatingObservation alternating_unit.1

theorem alternating_fixed_limit_criterion (u a : ℝ) :
    Tendsto (fun T : ℕ => comparatorRegret
      (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) u T / (T : ℝ)) atTop (nhds a) ↔
    Tendsto (fun T : ℕ => (u - empiricalMean alternatingObservation T)^2)
      atTop (nhds (-a)) := by
  exact meanPredict_fixedRegret_limit_iff alternatingObservation alternating_unit.1 u a

theorem alternating_fixed_zero_negative_limit :
    Tendsto (fun T : ℕ => comparatorRegret
      (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) 0 T / (T : ℝ))
      atTop (nhds (-(1 : ℝ) / 4)) := by
  have h := (meanPredict_limitNoRegret_of_mean_converges alternatingObservation
    alternating_unit.1 ((1 : ℝ) / 2) alternating_mean_tendsto).1 0
  norm_num at h ⊢
  exact h

theorem alternating_fixed_half_zero_limit :
    Tendsto (fun T : ℕ => comparatorRegret
      (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) ((1 : ℝ) / 2) T / (T : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have h := (meanPredict_limitNoRegret_of_mean_converges alternatingObservation
    alternating_unit.1 ((1 : ℝ) / 2) alternating_mean_tendsto).1 ((1 : ℝ) / 2)
  simpa using h

theorem alternating_literal_limit_noRegret :
    LimitNoRegret (Set.Icc (0 : ℝ) 1)
      (fun t x => (x - alternatingObservation t)^2) (meanPredict alternatingObservation) := by
  exact (meanPredict_limitNoRegret_of_mean_converges alternatingObservation
    alternating_unit.1 ((1 : ℝ) / 2) alternating_mean_tendsto).2

end Tests.OnlineFTLLimitSemantics
