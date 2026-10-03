import BanditRLProof.HeavyTailSourceConfidence

/-! Original source log schedule and signed adaptive-prefix confidence.
Counts are handled by a finite union, never by asserting selected samples IID. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

noncomputable def sourceConfidenceLog (t : ℕ) : ℝ := 2*Real.log ((t : ℝ)+1)

noncomputable def sourceConfidenceRadius (ε u : ℝ) (t n : ℕ) : ℝ :=
  4*u^(1/(1+ε))*(sourceConfidenceLog t/n)^(ε/(1+ε))

theorem sourceConfidenceLog_pos (t : ℕ) (ht : 0 < t) : 0 < sourceConfidenceLog t := by
  apply mul_pos (by norm_num) (Real.log_pos _)
  exact_mod_cast (show 1 < t+1 by omega)

/-- The count is arbitrary; the set explicitly restricts it to the available prefixes. -/
theorem source_adaptive_mean_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (count : Ω → ℕ) (ε u mean : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 0 < count ω ∧ count ω ≤ t ∧
      sourceConfidenceRadius ε u t (count ω) ≤
        (∑ s ∈ Finset.range (count ω),
          truncate (sourceTruncationThreshold ε u (sourceConfidenceLog t) s) (X s ω)) /
            count ω - mean} ≤ t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  by_cases ht : t = 0
  · subst t
    have hempty : ∀ ω, ¬(0 < count ω ∧ count ω ≤ 0) := by intro ω; omega
    simp only [← and_assoc, hempty, false_and, Set.setOf_false, measureReal_empty,
      Nat.cast_zero, zero_mul, le_refl]
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  let E := fun k => {ω | sourceConfidenceRadius ε u t (k+1) ≤
    (∑ s ∈ Finset.range (k+1),
      truncate (sourceTruncationThreshold ε u (sourceConfidenceLog t) s) (X s ω)) /
        ((k+1 : ℕ) : ℝ) - mean}
  have hs : {ω | 0 < count ω ∧ count ω ≤ t ∧
      sourceConfidenceRadius ε u t (count ω) ≤
        (∑ s ∈ Finset.range (count ω),
          truncate (sourceTruncationThreshold ε u (sourceConfidenceLog t) s) (X s ω)) /
            count ω - mean} ⊆ ⋃ k ∈ Finset.range t, E k := by
    intro ω hω
    rcases hω with ⟨hpos, hle, hbad⟩
    apply Set.mem_iUnion.mpr ⟨count ω - 1, ?_⟩
    apply Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have he : count ω - 1 + 1 = count ω := by omega
    simpa only [E, Set.mem_setOf_eq, he] using hbad
  calc
    _ ≤ μ.real (⋃ k ∈ Finset.range t, E k) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range t, μ.real (E k) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range t, Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
      apply Finset.sum_le_sum
      intro k _
      exact source_truncated_mean_upper_tail_log_sharp μ X ε u (sourceConfidenceLog t)
        mean (k+1) (by omega) hXm hi hε0 hε hu (sourceConfidenceLog_pos t htpos)
        hX hmean hm hraw
    _ = _ := by simp

/-- Reflection retains the identical count, schedule and raw moment hypotheses. -/
theorem source_adaptive_mean_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (count : Ω → ℕ) (ε u mean : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 0 < count ω ∧ count ω ≤ t ∧
      sourceConfidenceRadius ε u t (count ω) ≤
        mean - (∑ s ∈ Finset.range (count ω),
          truncate (sourceTruncationThreshold ε u (sourceConfidenceLog t) s) (X s ω)) /
            count ω} ≤ t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  have h := source_adaptive_mean_upper_tail μ (fun i ω => -X i ω) count ε u (-mean) t
    (fun i => (hXm i).neg) (hi.comp (fun _ x => -x) (fun _ => measurable_neg))
    hε0 hε hu (fun i => (hX i).neg)
    (fun i => by rw [integral_neg, hmean i])
    (fun i => by simpa only [abs_neg] using hm i)
    (fun i => by simpa only [abs_neg] using hraw i)
  simpa only [truncate_neg, Finset.sum_neg_distrib, neg_div, sub_neg_eq_add, neg_add_eq_sub]
    using h

theorem inverse_sqrt_step (x : ℝ) (hx : 0 < x) :
    1 / (Real.sqrt (x+1))^3 ≤
      2*(1/Real.sqrt x - 1/Real.sqrt (x+1)) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x+1)
  have ha : 0 < a := Real.sqrt_pos.mpr hx
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a^2 = x := Real.sq_sqrt hx.le
  have hb2 : b^2 = x+1 := Real.sq_sqrt (by linarith)
  have hid : 2*(1/a-1/b) = 2/(a*b*(a+b)) := by
    field_simp
    nlinarith [ha2, hb2]
  change 1 / b^3 ≤ 2*(1/a-1/b)
  rw [hid]
  apply (div_le_div_iff₀ (pow_pos hb 3) (by positivity : 0 < a*b*(a+b))).mpr
  have hprod : a*b*(a+b) ≤ b*b*(2*b) := by
    gcongr; linarith
  nlinarith


theorem source_schedule_exp_eq (t : ℕ) :
    Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) = 1/(Real.sqrt ((t : ℝ)+1))^5 := by
  have hp : 0 < (t : ℝ)+1 := by positivity
  have he : (Real.sqrt ((t : ℝ)+1))^5 = ((t : ℝ)+1)^(5/2 : ℝ) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hp.le]
    norm_num
  rw [he]
  unfold sourceConfidenceLog
  rw [show -(5/4 : ℝ)*(2*Real.log ((t : ℝ)+1)) =
    Real.log ((t : ℝ)+1)*(-(5/2 : ℝ)) by ring, ← Real.rpow_def_of_pos hp,
    Real.rpow_neg hp.le, one_div]

theorem source_schedule_tail_le_telescope (t : ℕ) (ht : 0 < t) :
    t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) ≤
      2*(1/Real.sqrt (t : ℝ)-1/Real.sqrt ((t : ℝ)+1)) := by
  rw [source_schedule_exp_eq]
  apply le_trans ?_ (inverse_sqrt_step (t : ℝ) (Nat.cast_pos.mpr ht))
  have hb : 0 < Real.sqrt ((t : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hb2 := Real.sq_sqrt (show 0 ≤ (t : ℝ)+1 by positivity)
  apply (mul_le_mul_iff_right₀ (pow_pos hb 5)).mp
  field_simp
  nlinarith

theorem source_schedule_tail_sum_le_two (T : ℕ) :
    (∑ t ∈ Finset.range T, t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t)) ≤ 2 := by
  have hshift : ∀ n : ℕ,
      (∑ s ∈ Finset.range n, (s+1 : ℝ)*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog (s+1))) ≤
        2*(1-1/Real.sqrt ((n : ℝ)+1)) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := source_schedule_tail_le_telescope (n+1) (by omega)
      push_cast at h ⊢
      linarith
  cases T with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    have h := hshift n
    push_cast
    simp only [zero_mul, add_zero]
    exact h.trans (by
      have : 0 ≤ 1/Real.sqrt ((n : ℝ)+1) := by positivity
      linarith)

end BanditRLProof.HeavyTail
