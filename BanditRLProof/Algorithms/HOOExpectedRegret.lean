import BanditRLProof.Algorithms.HOORegretPartition

/-! Integrability and the unoptimized expected HOO regret bound, on the actual
trajectory. Mean boundedness is a native source-model hypothesis. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem RegularCovering.integrable_actual_gap {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ)
    (hfrange : ∀x, f x ∈ Set.Icc (0:ℝ) 1)
    (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ] (n : ℕ) :
    Integrable (fun Y => best-f (C.toCovering.arm C.nu1 C.rho Y n)) μ := by
  have hm : Measurable (fun Y => best-f (C.toCovering.arm C.nu1 C.rho Y n)) :=
    (measurable_of_countable (fun v : Node => best-f (C.toCovering.representative v))).comp
      (measurable_action C.nu1 C.rho n)
  apply Integrable.of_bound hm.aestronglyMeasurable (|best|+1)
  apply ae_of_all
  intro Y
  have hr := hfrange (C.toCovering.arm C.nu1 C.rho Y n)
  have hn : ‖f (C.toCovering.arm C.nu1 C.rho Y n)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr.1]; exact hr.2
  exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs] using add_le_add (le_refl ‖best‖) hn)

/-- Expected regret with an arbitrary integer cutoff H, retaining the exact
three terms. All random count bounds come from the actual HOO law. -/
theorem RegularCovering.expected_regret_partition_bound {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀x, (∫ y, y ∂law x)=f x)
    (hf : ∀x, f x≤best) (hfrange : ∀x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1) (H N : ℕ) :
    (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
    4*(C.nu1*C.rho^H)*N +
    (∑ h ∈ Finset.range H, 4*(C.nu1*C.rho^h)*(C.nearOptimalNodes f best h).card) +
    ∑ h ∈ Finset.range H, 4*(C.nu1*C.rho^h)*(C.boundaryNodes f best h).card *
      (8*Real.log (max (N:ℝ) 2)/(C.nu1*C.rho^(h+1))^2+4) := by
  let μ := trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)
  let D := fun h => 4*(C.nu1*C.rho^h)
  let A := D H*N + ∑ h ∈ Finset.range H, D h*(C.nearOptimalNodes f best h).card
  let V := fun (p : Node) (Y : ℕ → ℝ) => (visits (history C.nu1 C.rho Y N) p : ℝ)
  have hV (p : Node) : Integrable (V p) μ := integrable_visits C.nu1 C.rho p μ N
  have hDV (h : ℕ) (p : Node) : Integrable (fun Y => D h*V p Y) μ := (hV p).const_mul _
  have hS (h : ℕ) : Integrable (fun Y => ∑ p ∈ C.boundaryNodes f best h, D h*V p Y) μ :=
    integrable_finset_sum _ (fun p _ => hDV h p)
  have hSS : Integrable (fun Y => ∑ h ∈ Finset.range H,
      ∑ p ∈ C.boundaryNodes f best h, D h*V p Y) μ :=
    integrable_finset_sum _ (fun h _ => hS h)
  have hleft : Integrable (fun Y => ∑ n ∈ Finset.range N,
      (best-f (C.toCovering.arm C.nu1 C.rho Y n))) μ :=
    integrable_finset_sum _ (fun n _ => C.integrable_actual_gap f best hfrange μ n)
  have hi := integral_mono hleft ((integrable_const A).add hSS)
    (fun Y => C.pathwise_regret_le f best hf hbest hw H N Y)
  have he : (∫ Y, A + ∑ h ∈ Finset.range H, ∑ p ∈ C.boundaryNodes f best h,
      D h*V p Y ∂μ) = A + ∑ h ∈ Finset.range H, ∑ p ∈ C.boundaryNodes f best h,
        D h*(∫ Y, V p Y ∂μ) := by
    rw [integral_add (integrable_const A) hSS, integral_const, probReal_univ, one_smul,
      integral_finset_sum _ (fun h _ => hS h)]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    rw [integral_finset_sum _ (fun p _ => hDV h p)]
    apply Finset.sum_congr rfl
    intro p hp
    exact integral_const_mul _ _
  simp only [Pi.add_apply] at hi
  rw [he] at hi
  apply hi.trans
  refine add_le_add (le_refl A) ?_
  calc
    _ ≤ ∑ h ∈ Finset.range H, ∑ _p ∈ C.boundaryNodes f best h,
        D h*(8*Real.log (max (N:ℝ) 2)/(C.nu1*C.rho^(h+1))^2+4) := by
      apply Finset.sum_le_sum; intro h hh
      apply Finset.sum_le_sum; intro p hp
      exact mul_le_mul_of_nonneg_left
        (C.boundary_expected_visits law f best hmean hf hbest hw hbound hp N)
        (mul_nonneg (by norm_num) (mul_pos C.nu1_pos (pow_pos C.rho_pos _)).le)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp only [D]
      ring


/-- Definition-5 dimension supplies one constant for every cutoff and horizon;
the remaining finite geometric sums are explicit, not hidden in an O premise. -/
theorem RegularCovering.expected_regret_dimension_sums {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best d : ℝ) (hmean : ∀x, (∫ y, y ∂law x)=f x)
    (hf : ∀x, f x≤best) (hfrange : ∀x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ K : ℝ, 0<K ∧ ∀ H N : ℕ,
    (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
    4*(C.nu1*C.rho^H)*N +
    (∑ h ∈ Finset.range H, 4*(C.nu1*C.rho^h)*(K*(C.nu2*C.rho^h)^(-d))) +
    ∑ h ∈ Finset.range H, 8*(C.nu1*C.rho^h)*(K*(C.nu2*C.rho^h)^(-d)) *
      (8*Real.log (max (N:ℝ) 2)/(C.nu1*C.rho^(h+1))^2+4) := by
  obtain ⟨K, hK, hI⟩ := C.nearOptimalNodes_power_bound f best d hw hd
  refine ⟨K, hK, fun H N => ?_⟩
  have hD (h : ℕ) : 0≤C.nu1*C.rho^h := (mul_pos C.nu1_pos (pow_pos C.rho_pos _)).le
  have hJ (h : ℕ) : ((C.boundaryNodes f best h).card : ℝ) ≤
      2*(K*(C.nu2*C.rho^h)^(-d)) := by
    have hh : ((C.boundaryNodes f best h).card : ℝ) ≤ 2*(C.nearOptimalNodes f best h).card := by
      exact_mod_cast C.boundaryNodes_card_le f best h
    exact hh.trans (mul_le_mul_of_nonneg_left (hI h) (by norm_num))
  apply (C.expected_regret_partition_bound law f best hmean hf hfrange hbest hw hbound H N).trans
  apply add_le_add
  · apply add_le_add (le_refl _)
    apply Finset.sum_le_sum
    intro h hh
    exact mul_le_mul_of_nonneg_left (hI h) (mul_nonneg (by norm_num) (hD h))
  · apply Finset.sum_le_sum
    intro h hh
    have hB : 0≤8*Real.log (max (N:ℝ) 2)/(C.nu1*C.rho^(h+1))^2+4 := by
      have hL : 0≤Real.log (max (N:ℝ) 2) := Real.log_nonneg (le_max_of_le_right (by norm_num))
      positivity
    have he := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hJ h) (mul_nonneg (by norm_num : (0:ℝ)≤4) (hD h))) hB
    convert he using 1 <;> ring

end BanditRLProof.HOO

