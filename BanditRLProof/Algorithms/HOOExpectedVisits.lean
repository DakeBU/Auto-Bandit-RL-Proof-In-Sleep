import BanditRLProof.Algorithms.HOOSelectionTail
import BanditRLProof.HOOTailSum
import BanditRLProof.Algorithms.HeavyTailExpectedCount

/-! Expected HOO regional visits through the shared threshold-count argument.
The binary trace below records visits to one fixed region; it does not replace
the infinite HOO action space or its reward trajectory by a finite-arm model. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory

noncomputable def visitTrace (ν ρ : ℝ) (v : Node) (Y : ℕ → ℝ) : ActionTrace (Fin 2) :=
  fun i => if v <+: action ν ρ Y i then 0 else 1

theorem measurable_visitTrace (ν ρ : ℝ) (v : Node) (i : ℕ) :
    Measurable (fun Y => visitTrace ν ρ v Y i) :=
  (measurable_of_countable (f := fun a : Node => if v <+: a then (0 : Fin 2) else 1)).comp
    (measurable_action ν ρ i)

@[simp] theorem visitTrace_zero_iff (ν ρ : ℝ) (v : Node) (Y : ℕ → ℝ) (i : ℕ) :
    visitTrace ν ρ v Y i = 0 ↔ v <+: action ν ρ Y i := by
  unfold visitTrace
  split_ifs <;> simp_all

theorem visitTrace_pullCount (ν ρ : ℝ) (v : Node) (Y : ℕ → ℝ) (n : ℕ) :
    pullCount (visitTrace ν ρ v Y) 0 n = visits (history ν ρ Y n) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pullCount_succ, ih, history, visits_step]
    simp only [visitTrace_zero_iff, action]

theorem lintegral_visits_threshold (ν ρ : ℝ) (v : Node) (μ : Measure (ℕ → ℝ))
    [IsProbabilityMeasure μ] (N B : ℕ) :
    (∫⁻ Y, (visits (history ν ρ Y N) v : ENNReal) ∂μ) ≤
      B + ∑ n ∈ Finset.range N, μ {Y | v <+: action ν ρ Y n ∧ B ≤ visits (history ν ρ Y n) v} := by
  simpa only [visitTrace_pullCount, visitTrace_zero_iff] using
    HeavyTail.lintegral_pullCount_threshold μ (visitTrace ν ρ v) (measurable_visitTrace ν ρ v) 0 N B

noncomputable def visitThreshold (gap : ℝ) (N : ℕ) : ℕ :=
  ⌈8*Real.log (max (N:ℝ) 2)/gap^2⌉₊

theorem visitThreshold_controls (gap : ℝ) (N n : ℕ) (hn : n ≤ N) :
    8*Real.log (max (n:ℝ) 2)/gap^2 ≤ (visitThreshold gap N : ℝ) := by
  apply le_trans _ (Nat.le_ceil _)
  apply div_le_div_of_nonneg_right _ (sq_nonneg gap)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log (lt_max_of_lt_right (by norm_num))
  exact max_le_max (by exact_mod_cast hn) le_rfl

theorem RegularCovering.poor_region_lintegral_visits {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x) = f x)
    (hf : ∀ x, f x ≤ best) (hbest : regionSup f Set.univ = best)
    (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (hv : C.nu1*C.rho^v.length < best-regionSup f (C.region v)) (N : ℕ) :
    (∫⁻ Y, (visits (history C.nu1 C.rho Y N) v : ENNReal)
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
      visitThreshold (best-regionSup f (C.region v)-C.nu1*C.rho^v.length) N + 3 := by
  apply (lintegral_visits_threshold C.nu1 C.rho v _ N
    (visitThreshold (best-regionSup f (C.region v)-C.nu1*C.rho^v.length) N)).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (selectionFailureBudget n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := C.poor_region_selection_tail law f best hmean hf hbest hw hbound v hv n
      have he : ENNReal.ofReal (selectionFailureBudget n) =
          ((n:ENNReal)+2)*((n:ENNReal)*ENNReal.ofReal (Real.exp (-4*Real.log (max (n:ℝ) 2)))) := by
        unfold selectionFailureBudget
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
        ring
      rw [he]
      refine (measure_mono ?_).trans hh
      intro Y hY
      exact ⟨(visitThreshold_controls _ N n (Finset.mem_range.mp hn).le).trans
        (by exact_mod_cast hY.2), hY.1⟩
    _ = ENNReal.ofReal (∑ n ∈ Finset.range N, selectionFailureBudget n) :=
      (ENNReal.ofReal_sum_of_nonneg (fun n _ => by unfold selectionFailureBudget; positivity)).symm
    _ ≤ 3 := by exact_mod_cast ENNReal.ofReal_le_ofReal (selection_failure_sum_le_three N)

theorem integrable_visits (ν ρ : ℝ) (v : Node) (μ : Measure (ℕ → ℝ))
    [IsProbabilityMeasure μ] (N : ℕ) :
    Integrable (fun Y => (visits (history ν ρ Y N) v : ℝ)) μ := by
  have hm : Measurable (fun Y => (visits (history ν ρ Y N) v : ℝ)) := by
    simpa only [visitTrace_pullCount] using
      measurable_natCast_pullCount (visitTrace ν ρ v) (measurable_visitTrace ν ρ v) 0 N
  apply Integrable.of_bound hm.aestronglyMeasurable (N:ℝ)
  apply ae_of_all
  intro Y
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast visits_history_le ν ρ v N Y

/-- Expected poor-region visits, with the source additive-four shape and an
explicit logarithm repair at horizons zero and one. All probability and search
premises are produced from the actual HOO algorithm and A1/A2 model. -/
theorem RegularCovering.poor_region_expected_visits {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x) = f x)
    (hf : ∀ x, f x ≤ best) (hbest : regionSup f Set.univ = best)
    (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (hv : C.nu1*C.rho^v.length < best-regionSup f (C.region v)) (N : ℕ) :
    (∫ Y, (visits (history C.nu1 C.rho Y N) v : ℝ)
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
      8*Real.log (max (N:ℝ) 2)/(best-regionSup f (C.region v)-C.nu1*C.rho^v.length)^2 + 4 := by
  have h := C.poor_region_lintegral_visits law f best hmean hf hbest hw hbound v hv N
  have he := ofReal_integral_eq_lintegral_ofReal (integrable_visits C.nu1 C.rho v
    (trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) N)
    (ae_of_all _ (fun Y => Nat.cast_nonneg (visits (history C.nu1 C.rho Y N) v)))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he] at h
  have hr := (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp h
  have hreal : (∫ Y, (visits (history C.nu1 C.rho Y N) v : ℝ)
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
      (visitThreshold (best-regionSup f (C.region v)-C.nu1*C.rho^v.length) N : ℝ) + 3 := by
    simpa using hr
  have hL : 0 ≤ Real.log (max (N:ℝ) 2) := Real.log_nonneg (le_max_of_le_right (by norm_num))
  have hc := Nat.ceil_lt_add_one (show 0 ≤
    8*Real.log (max (N:ℝ) 2)/(best-regionSup f (C.region v)-C.nu1*C.rho^v.length)^2 by positivity)
  unfold visitThreshold at hreal
  linarith

end BanditRLProof.HOO
