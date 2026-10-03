import BanditRLProof.Algorithms.MusicalChairsCoordination
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! Quantitative continuation of the actual static coordination kernel.
This module does not provide the exploration-good event or the full learner. -/
namespace BanditRLProof.MusicalChairs
open scoped Classical ENNReal
set_option autoImplicit false

theorem quarter_le_avoidance_succ (m : ℕ) (hm : 0 < m) :
    (1/4 : ℝ) ≤ ((m : ℝ) / ((m : ℝ)+1))^m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : 0 < (m : ℝ) / ((m : ℝ)+1) := div_pos hmR (by linarith)
  have hl := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hmR.le
  have heq : (m : ℝ) * (1 - ((m : ℝ) / ((m : ℝ)+1))⁻¹) = -1 := by
    field_simp
    ring
  rw [heq] at hl
  calc
    (1/4 : ℝ) ≤ (Real.exp 1)⁻¹ := by
      have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_three.le.trans (by norm_num)
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 1) he
    _ = Real.exp (-1) := (Real.exp_neg 1).symm
    _ ≤ Real.exp ((m : ℝ) * Real.log ((m : ℝ) / ((m : ℝ)+1))) := Real.exp_le_exp.mpr hl
    _ = ((m : ℝ) / ((m : ℝ)+1))^m := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hx _)]

theorem quarter_le_avoidance (n : ℕ) (hn : 2 ≤ n) :
    (1/4 : ℝ) ≤ (((n-1 : ℕ) : ℝ) / (n : ℝ))^(n-1) := by
  have heq : n = (n-1)+1 := by omega
  convert quarter_le_avoidance_succ (n-1) (by omega) using 1
  congr 2
  exact_mod_cast heq

theorem real_uniform_hazard_lower (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (4 * n) ≤
      (1 / (n : ℝ)) * (((n-1 : ℕ) : ℝ) / (n : ℝ))^(n-1) := by
  by_cases h : n = 1
  · subst n; norm_num
  have hq := mul_le_mul_of_nonneg_left (quarter_le_avoidance n (by omega))
    (show (0 : ℝ) ≤ 1 / n by positivity)
  convert hq using 1
  ring

theorem uniform_hazard_lower (n : ℕ) (hn : 0 < n) :
    (1 : ℝ≥0∞) / (4 * n) ≤
      (1 / (n : ℝ≥0∞)) * (((n-1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞))^(n-1) := by
  have h := ENNReal.ofReal_le_ofReal (real_uniform_hazard_lower n hn)
  simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 4*n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/n),
    ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < n),
    ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ ((n-1:ℕ):ℝ)/(n:ℝ))] using h

theorem transition_unfixed_hazard_quarter {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (s : State n k) (i : Fin n) (hi : s i = none)
    (hcard : S.card = n) :
    (1 : ℝ≥0∞) / (4 * n) ≤
      (transition (fun _ : Fin n => S) (fun _ => hne) s).toOuterMeasure
        {s' | s' i ≠ none} :=
  (uniform_hazard_lower n (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)).trans
    (transition_unfixed_hazard S hne s i hi hcard)

theorem event_add_compl {α : Type*} (p : PMF α) (E : Set α) :
    p.toOuterMeasure E + p.toOuterMeasure Eᶜ = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  calc
    _ = ∑' a, p a := by
      apply tsum_congr
      intro a
      by_cases h : a ∈ E <;> simp [Set.indicator, h]
    _ = 1 := p.tsum_coe

theorem transition_fixed_no_return {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ j, (candidates j).Nonempty) (s : State n k) (i : Fin n)
    (hi : s i ≠ none) :
    (transition candidates hne s).toOuterMeasure {s' | s' i = none} = 0 := by
  apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
  rw [Set.disjoint_left]
  intro s' hs' hn
  obtain ⟨draw, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs'
  cases hsi : s i with
  | none => exact hi hsi
  | some a => simp [step, hsi] at hn

theorem transition_unfixed_le {n k : ℕ} (S : Finset (Fin k)) (hne : S.Nonempty)
    (s : State n k) (i : Fin n) (hcard : S.card = n) :
    (transition (fun _ : Fin n => S) (fun _ => hne) s).toOuterMeasure
      {s' | s' i = none} ≤ if s i = none then 1 - (1 : ℝ≥0∞)/(4*n) else 0 := by
  by_cases hi : s i = none
  · rw [if_pos hi]
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hq := transition_unfixed_hazard_quarter S hne s i hi hcard
    have he := event_add_compl (transition (fun _ : Fin n => S) (fun _ => hne) s)
      {s' | s' i = none}
    have hfinite : (1 : ℝ≥0∞)/(4*n) ≠ ∞ := by simp [div_eq_mul_inv, hn.ne']
    apply ENNReal.le_sub_of_add_le_right hfinite
    calc
      _ ≤ (transition (fun _ : Fin n => S) (fun _ => hne) s).toOuterMeasure
            {s' | s' i = none} +
          (transition (fun _ : Fin n => S) (fun _ => hne) s).toOuterMeasure
            {s' | s' i ≠ none} := add_le_add le_rfl hq
      _ = 1 := he
  · rw [if_neg hi, transition_fixed_no_return _ _ s i hi]

theorem unfixed_survival {n k : ℕ} (S : Finset (Fin k)) (hne : S.Nonempty)
    (i : Fin n) (hcard : S.card = n) (t : ℕ) :
    (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).toOuterMeasure
      {s | s i = none} ≤ (1 - (1 : ℝ≥0∞)/(4*n))^t := by
  induction t with
  | zero => simp only [stateLaw, PMF.toOuterMeasure_pure_apply, initial,
      Set.mem_setOf_eq, ite_true, pow_zero, le_refl]
  | succ t ih =>
    rw [stateLaw, PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' s, (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
          (if s i = none then 1 - (1 : ℝ≥0∞)/(4*n) else 0) := by
        apply ENNReal.tsum_le_tsum
        intro s
        gcongr
        exact transition_unfixed_le S hne s i hcard
      _ = (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).toOuterMeasure
          {s | s i = none} * (1 - (1 : ℝ≥0∞)/(4*n)) := by
        rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro s
        by_cases h : s i = none <;> simp [h, Set.indicator]
      _ ≤ (1 - (1 : ℝ≥0∞)/(4*n))^t * (1 - (1 : ℝ≥0∞)/(4*n)) :=
        by gcongr
      _ = _ := (pow_succ _ _).symm

theorem quarter_rate_le_one (n : ℕ) (hn : 0 < n) :
    (1 : ℝ≥0∞) / (4*n) ≤ 1 := by
  rw [one_div, ENNReal.inv_le_one]
  have h : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast hn
  calc
    (1 : ℝ≥0∞) ≤ 4 * 1 := by norm_num
    _ ≤ 4 * n := by gcongr

theorem unfixed_survival_sum {n k : ℕ} (S : Finset (Fin k)) (hne : S.Nonempty)
    (i : Fin n) (hcard : S.card = n) (T : ℕ) :
    ∑ t ∈ Finset.range T,
      (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).toOuterMeasure
        {s | s i = none} ≤ 4*n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  calc
    _ ≤ ∑ t ∈ Finset.range T, (1 - (1 : ℝ≥0∞)/(4*n))^t :=
      Finset.sum_le_sum (fun t _ => unfixed_survival S hne i hcard t)
    _ ≤ ∑' t : ℕ, (1 - (1 : ℝ≥0∞)/(4*n))^t := ENNReal.sum_le_tsum _
    _ = 4*n := by
      rw [ENNReal.tsum_geometric,
        ENNReal.sub_sub_cancel (by simp) (quarter_rate_le_one n hn)]
      simp [one_div]

/-- Expected total unfixed occupancy, expressed by actual finite-time marginals.
The full pathwise regret adapter is a separate obligation. -/
theorem total_unfixed_occupation_le {n k : ℕ} (S : Finset (Fin k)) (hne : S.Nonempty)
    (hcard : S.card = n) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ i : Fin n,
      (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).toOuterMeasure
        {s | s i = none} ≤ 4*(n : ℝ≥0∞)^2 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : Fin n, (4*n : ℝ≥0∞) :=
      Finset.sum_le_sum (fun i _ => unfixed_survival_sum S hne i hcard T)
    _ = _ := by simp [pow_two]; ring

noncomputable def unfixedCount {n k : ℕ} (s : State n k) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => s i = none)).card

theorem unfixedCount_eq_sum {n k : ℕ} (s : State n k) :
    (unfixedCount s : ℝ≥0∞) = ∑ i : Fin n, if s i = none then 1 else 0 := by
  simp only [unfixedCount, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter, apply_ite, Nat.cast_zero]

theorem expected_unfixed_eq_prob_sum {n k : ℕ} (p : PMF (State n k)) :
    ∑ s, p s * (unfixedCount s : ℝ≥0∞) =
      ∑ i : Fin n, p.toOuterMeasure {s | s i = none} := by
  simp_rw [unfixedCount_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [PMF.toOuterMeasure_apply_fintype]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : s i = none <;> simp [h, Set.indicator]

/-- Finite cumulative expected occupancy of the actual recursive state law.
Counts are charged before each transition, including the initial all-unfixed state. -/
theorem expected_unfixed_occupation_le {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (hcard : S.card = n) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s,
      (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
        (unfixedCount s : ℝ≥0∞) ≤ 4*(n : ℝ≥0∞)^2 := by
  simp_rw [expected_unfixed_eq_prob_sum]
  exact total_unfixed_occupation_le S hne hcard T

end BanditRLProof.MusicalChairs
