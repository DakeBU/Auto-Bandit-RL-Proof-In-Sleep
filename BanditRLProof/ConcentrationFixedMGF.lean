import Mathlib.Probability.Moments.SubGaussian

/-!
# Fixed-tilt conditional MGF concentration

This module isolates the part of a martingale Bernstein/Freedman route that does not depend on
the particular one-step exponential inequality.  Unlike `HasSubgaussianMGF`, the upper bound is
required at one fixed tilt only.  Exponential integrability at every real multiple is retained
because it is the regularity needed to compose kernel laws.
-/

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.Concentration

namespace Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : ProbabilityTheory.Kernel Ω' Ω} {X : Ω → ℝ} {t ψ : ℝ}

/-- A kernel-valued MGF upper bound at one fixed tilt.  Integrability is required at every tilt
so that successive conditional laws can be composed without adding boundedness assumptions. -/
structure HasMGFUpperBoundAt (X : Ω → ℝ) (t ψ : ℝ)
    (κ : ProbabilityTheory.Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ s, Integrable (fun ω ↦ exp (s * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ProbabilityTheory.mgf X (κ ω') t ≤ exp ψ

namespace HasMGFUpperBoundAt

lemma ae_integrable_exp_mul (h : HasMGFUpperBoundAt X t ψ κ ν) (s : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (s * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul s)

lemma ae_forall_integrable_exp_mul (h : HasMGFUpperBoundAt X t ψ κ ν) :
    ∀ᵐ ω' ∂ν, ∀ s, Integrable (fun ω ↦ exp (s * X ω)) (κ ω') := by
  have h_int (n : ℤ) : ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int s
  exact ProbabilityTheory.integrable_exp_mul_of_le_of_le
    (h_int _) (h_int _) (Int.floor_le s) (Int.le_ceil s)

lemma congr {Y : Ω -> Real} (h : HasMGFUpperBoundAt X t ψ κ ν)
    (hXY : X =ᵐ[κ ∘ₘ ν] Y) : HasMGFUpperBoundAt Y t ψ κ ν where
  integrable_exp_mul s := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul s)
    filter_upwards [hXY] with omega homega
    rw [homega]
  mgf_le := by
    have hkernel := Measure.ae_ae_of_ae_comp hXY
    filter_upwards [h.mgf_le, hkernel] with omega hmgf heq
    rw [ProbabilityTheory.mgf_congr (Filter.EventuallyEq.symm heq)]
    exact hmgf

lemma congr_iff {Y : Ω -> Real} (hXY : X =ᵐ[κ ∘ₘ ν] Y) :
    HasMGFUpperBoundAt X t ψ κ ν ↔ HasMGFUpperBoundAt Y t ψ κ ν :=
  ⟨fun hX => hX.congr hXY, fun hY => hY.congr hXY.symm⟩

lemma memLp_exp_mul (h : HasMGFUpperBoundAt X t ψ κ ν) (s : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (s * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul s).1
  constructor
  · exact (h.integrable_exp_mul s).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * s)).2
    rw [hasFiniteIntegral_def] at h'
    convert h' using 3 with ω
    rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity), ← exp_mul, mul_comm, ← mul_assoc]
    positivity

@[simp]
lemma zero_kernel : HasMGFUpperBoundAt X t ψ (0 : ProbabilityTheory.Kernel Ω' Ω) ν := by
  constructor
  · simp
  · simpa using ae_of_all ν (fun _ ↦ (Real.exp_pos ψ).le)

@[simp]
lemma zero_measure : HasMGFUpperBoundAt X t ψ κ (0 : Measure Ω') := by
  constructor
  · simp
  · simp

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' → ℝ} {ψY : ℝ}

lemma prodMkLeft_compProd {η : ProbabilityTheory.Kernel Ω Ω''}
    (h : HasMGFUpperBoundAt Y t ψY η (κ ∘ₘ ν)) :
    HasMGFUpperBoundAt Y t ψY (ProbabilityTheory.Kernel.prodMkLeft Ω' η) (ν ⊗ₘ κ) := by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : ProbabilityTheory.IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd, Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

variable [SFinite ν]

lemma integrable_exp_add_compProd
    {η : ProbabilityTheory.Kernel (Ω' × Ω) Ω''}
    [ProbabilityTheory.IsZeroOrMarkovKernel η]
    (hX : HasMGFUpperBoundAt X t ψ κ ν)
    (hY : HasMGFUpperBoundAt Y t ψY η (ν ⊗ₘ κ)) (s : ℝ) :
    Integrable (fun ω ↦ exp (s * (X ω.1 + Y ω.2))) ((κ ⊗ₖ η) ∘ₘ ν) := by
  by_cases hκ : ProbabilityTheory.IsSFiniteKernel κ
  swap; · simp [hκ]
  rcases ProbabilityTheory.eq_zero_or_isMarkovKernel η with rfl | hη
  · simp
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have h := hX.memLp_exp_mul s 2
    simp only [ENNReal.coe_ofNat] at h
    have : κ ∘ₘ ν = ((κ ⊗ₖ η) ∘ₘ ν).map Prod.fst := by
      rw [Measure.map_comp _ _ measurable_fst, ← ProbabilityTheory.Kernel.fst_eq,
        ProbabilityTheory.Kernel.fst_compProd]
    rwa [this, memLp_map_measure_iff h.1 measurable_fst.aemeasurable] at h
  · have h := hY.memLp_exp_mul s 2
    rwa [ENNReal.coe_ofNat, Measure.comp_compProd_comm, Measure.snd,
      memLp_map_measure_iff h.1 measurable_snd.aemeasurable] at h

theorem add_compProd
    {η : ProbabilityTheory.Kernel (Ω' × Ω) Ω''}
    [ProbabilityTheory.IsZeroOrMarkovKernel η]
    (hX : HasMGFUpperBoundAt X t ψ κ ν)
    (hY : HasMGFUpperBoundAt Y t ψY η (ν ⊗ₘ κ)) :
    HasMGFUpperBoundAt (fun p ↦ X p.1 + Y p.2) t (ψ + ψY) (κ ⊗ₖ η) ν := by
  by_cases hκ : ProbabilityTheory.IsSFiniteKernel κ
  swap; · simp [hκ]
  refine ⟨integrable_exp_add_compProd hX hY, ?_⟩
  filter_upwards [hX.mgf_le, hX.ae_integrable_exp_mul t,
    Measure.ae_ae_of_ae_compProd hY.mgf_le,
    Measure.ae_integrable_of_integrable_comp <| integrable_exp_add_compProd hX hY t]
    with ω' hX_mgf hX_int hY_mgf h_int_mul
  calc ProbabilityTheory.mgf (fun p ↦ X p.1 + Y p.2) ((κ ⊗ₖ η) ω') t
  _ = ∫ x, exp (t * X x) * ∫ y, exp (t * Y y) ∂(η (ω', x)) ∂(κ ω') := by
    simp_rw [ProbabilityTheory.mgf, mul_add, exp_add] at h_int_mul ⊢
    simp_rw [integral_compProd h_int_mul, integral_const_mul]
  _ ≤ ∫ x, exp (t * X x) * exp ψY ∂(κ ω') := by
    refine integral_mono_of_nonneg ?_ (hX_int.mul_const _) ?_
    · exact ae_of_all _ fun _ ↦ mul_nonneg (by positivity)
        (integral_nonneg (fun _ ↦ by positivity))
    · filter_upwards [hY_mgf] with ω hY_mgf
      gcongr
      simpa [ProbabilityTheory.mgf] using hY_mgf
  _ ≤ exp (ψ + ψY) := by
    rw [integral_mul_const, exp_add]
    gcongr
    simpa [ProbabilityTheory.mgf] using hX_mgf

lemma add_comp {η : ProbabilityTheory.Kernel Ω Ω''}
    [ProbabilityTheory.IsZeroOrMarkovKernel η]
    (hX : HasMGFUpperBoundAt X t ψ κ ν)
    (hY : HasMGFUpperBoundAt Y t ψY η (κ ∘ₘ ν)) :
    HasMGFUpperBoundAt (fun p ↦ X p.1 + Y p.2) t (ψ + ψY)
      (κ ⊗ₖ ProbabilityTheory.Kernel.prodMkLeft Ω' η) ν :=
  hX.add_compProd hY.prodMkLeft_compProd

end HasMGFUpperBoundAt

end Kernel

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ}
  {μ : Measure Ω} {X : Ω → ℝ} {t ψ : ℝ}

/-- A measure-level MGF upper bound at one fixed tilt. -/
structure HasMGFUpperBoundAt (X : Ω → ℝ) (t ψ : ℝ)
    (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ s, Integrable (fun ω ↦ exp (s * X ω)) μ
  mgf_le : ProbabilityTheory.mgf X μ t ≤ exp ψ

lemma hasMGFUpperBoundAt_iff_kernel :
    HasMGFUpperBoundAt X t ψ μ ↔
      Kernel.HasMGFUpperBoundAt X t ψ
        (ProbabilityTheory.Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by simpa⟩,
    fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by simpa using h2⟩⟩

namespace HasMGFUpperBoundAt

lemma of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Z : Ω' → Ω} (hZ : AEMeasurable Z μ')
    (h : HasMGFUpperBoundAt X t ψ (μ'.map Z)) :
    HasMGFUpperBoundAt (X ∘ Z) t ψ μ' where
  integrable_exp_mul s := by
    have h1 := h.integrable_exp_mul s
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le := by
    convert h.mgf_le using 1
    rw [ProbabilityTheory.mgf_map hZ (h.integrable_exp_mul t).1]

lemma id_map_iff (hX : AEMeasurable X μ) :
    HasMGFUpperBoundAt id t ψ (μ.map X) ↔ HasMGFUpperBoundAt X t ψ μ := by
  refine ⟨fun h => ?_, fun h => ⟨fun s => ?_, ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul s
  · rw [ProbabilityTheory.mgf_id_map hX]
    exact h.mgf_le

/-- Subtracting a deterministic log-MGF budget turns a fixed-tilt bound into
a unit-tilt zero-budget bound. This is the algebraic step used to iterate
exponential supermartingale increments. -/
theorem compensated (h : HasMGFUpperBoundAt X t ψ μ) :
    HasMGFUpperBoundAt (fun ω => t * X ω - ψ) 1 0 μ := by
  constructor
  · intro s
    have hint := (h.integrable_exp_mul (s * t)).const_mul (Real.exp (-s * ψ))
    convert hint using 1
    funext ω
    calc
      Real.exp (s * (t * X ω - ψ)) =
          Real.exp (-s * ψ + (s * t) * X ω) := by congr 1; ring
      _ = Real.exp (-s * ψ) * Real.exp ((s * t) * X ω) := by
        rw [Real.exp_add]
  · rw [ProbabilityTheory.mgf]
    simp only [one_mul]
    simp_rw [sub_eq_add_neg, Real.exp_add]
    rw [integral_mul_const]
    calc
      (∫ ω, Real.exp (t * X ω) ∂μ) * Real.exp (-ψ) ≤
          Real.exp ψ * Real.exp (-ψ) := by
            gcongr
            simpa [ProbabilityTheory.mgf] using h.mgf_le
      _ = Real.exp 0 := by rw [← Real.exp_add]; simp

end HasMGFUpperBoundAt

variable [StandardBorelSpace Ω] [IsFiniteMeasure μ]

variable (m) (hm) in
/-- Conditional fixed-tilt MGF bound, expressed through Mathlib's conditional expectation kernel. -/
def HasCondMGFUpperBoundAt (X : Ω → ℝ) (t ψ : ℝ)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.HasMGFUpperBoundAt X t ψ (ProbabilityTheory.condExpKernel μ m) (μ.trim hm)

namespace HasMGFUpperBoundAt

omit [StandardBorelSpace Ω] [IsFiniteMeasure μ] in
lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : HasMGFUpperBoundAt X t ψ μ) :
    HasMGFUpperBoundAt X t ψ (μ.trim hm) where
  integrable_exp_mul s := by
    refine (hX.integrable_exp_mul s).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le := by
    rw [ProbabilityTheory.mgf, ← integral_trim]
    · exact hX.mgf_le
    · exact Measurable.stronglyMeasurable <| by fun_prop

theorem add_of_hasCondMGFUpperBoundAt {Y : Ω → ℝ} {ψX ψY : ℝ}
    (hm : m ≤ mΩ) (hX : HasMGFUpperBoundAt X t ψX (μ.trim hm))
    (hY : HasCondMGFUpperBoundAt m hm Y t ψY μ) :
    HasMGFUpperBoundAt (X + Y) t (ψX + ψY) μ := by
  suffices HasMGFUpperBoundAt (fun p ↦ X p.1 + Y p.2) t (ψX + ψY)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ) by
    have h_eq : X + Y = (fun p ↦ X p.1 + Y p.2) ∘ (fun ω ↦ (id ω, id ω)) := rfl
    rw [h_eq]
    refine HasMGFUpperBoundAt.of_map ?_ this
    exact @Measurable.aemeasurable _ _ _ (m.prod mΩ) _ _
      ((measurable_id'' hm).prodMk measurable_id)
  rw [hasMGFUpperBoundAt_iff_kernel] at hX ⊢
  have hY' : Kernel.HasMGFUpperBoundAt Y t ψY (ProbabilityTheory.condExpKernel μ m)
      (ProbabilityTheory.Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa
  convert hX.add_comp hY'
  ext
  rw [ProbabilityTheory.Kernel.const_apply, ← Measure.compProd,
    ProbabilityTheory.compProd_trim_condExpKernel]

omit [StandardBorelSpace Ω] in
lemma measure_ge_le_exp_add (h : HasMGFUpperBoundAt X t ψ μ) (ε : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε + ψ) := by
  calc μ.real {ω | ε ≤ X ω}
  _ ≤ exp (-t * ε) * ProbabilityTheory.mgf X μ t :=
    ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht (h.integrable_exp_mul t)
  _ ≤ exp (-t * ε + ψ) := by
    rw [exp_add]
    gcongr
    exact h.mgf_le

end HasMGFUpperBoundAt

variable {Y : ℕ → Ω → ℝ} {ψY : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}

theorem HasMGFUpperBoundAt.sum_of_hasCondMGFUpperBoundAt [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasMGFUpperBoundAt (Y 0) t (ψY 0) μ) (n : ℕ)
    (h_mgf : ∀ i < n - 1,
      HasCondMGFUpperBoundAt (ℱ i) (ℱ.le i) (Y (i + 1)) t (ψY (i + 1)) μ) :
    HasMGFUpperBoundAt (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) t
      (∑ i ∈ Finset.range n, ψY i) μ := by
  induction n with
  | zero =>
      constructor
      · simp
      · simpa [ProbabilityTheory.mgf] using (measureReal_le_one (μ := μ))
  | succ n hn =>
    induction n with
    | zero => simpa using h0
    | succ n =>
      specialize hn fun i hi ↦ h_mgf i (by omega)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasMGFUpperBoundAt.add_of_hasCondMGFUpperBoundAt (ℱ.le n) ?_ (h_mgf n (by omega))
      refine HasMGFUpperBoundAt.trim (ℱ.le n) ?_ hn
      refine Finset.measurable_fun_sum (Finset.range (n + 1)) fun j hj ↦
        ((h_adapted j).mono (ℱ.mono ?_)).measurable
      simp only [Finset.mem_range] at hj
      omega

/-- Fixed-tilt Chernoff bound for a strongly adapted finite sum with conditional MGF budgets. -/
theorem measure_sum_ge_le_of_hasCondMGFUpperBoundAt [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasMGFUpperBoundAt (Y 0) t (ψY 0) μ) (n : ℕ)
    (h_mgf : ∀ i < n - 1,
      HasCondMGFUpperBoundAt (ℱ i) (ℱ.le i) (Y (i + 1)) t (ψY (i + 1)) μ)
    (ε : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ exp (-t * ε + ∑ i ∈ Finset.range n, ψY i) :=
  (HasMGFUpperBoundAt.sum_of_hasCondMGFUpperBoundAt h_adapted h0 n h_mgf).measure_ge_le_exp_add ε ht

/--
Fixed-tilt tail bound with a random predictable compensator retained in the
event.  The conditional MGF hypotheses are imposed on the compensated
increments `tilt * Y i - varianceCoeff * V i`; on the event where the
cumulative compensator is at most `varianceBudget`, their exponential tail
controls the uncompensated sum.
-/
theorem measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
    [IsZeroOrProbabilityMeasure μ]
    (Y V : ℕ → Ω → ℝ) (n : ℕ) (tilt varianceCoeff threshold varianceBudget : ℝ)
    (h_adapted : StronglyAdapted ℱ
      (fun i ω => tilt * Y i ω - varianceCoeff * V i ω))
    (h0 : HasMGFUpperBoundAt
      (fun ω => tilt * Y 0 ω - varianceCoeff * V 0 ω) 1 0 μ)
    (h_mgf : ∀ i < n - 1,
      HasCondMGFUpperBoundAt (ℱ i) (ℱ.le i)
        (fun ω => tilt * Y (i + 1) ω - varianceCoeff * V (i + 1) ω)
        1 0 μ)
    (htilt : 0 ≤ tilt) (hvarianceCoeff : 0 ≤ varianceCoeff) :
    μ {ω |
        threshold ≤ ∑ i ∈ Finset.range n, Y i ω ∧
        (∑ i ∈ Finset.range n, V i ω) ≤ varianceBudget} ≤
      ENNReal.ofReal (Real.exp
        (-tilt * threshold + varianceCoeff * varianceBudget)) := by
  let Z : ℕ → Ω → ℝ := fun i ω =>
    tilt * Y i ω - varianceCoeff * V i ω
  let compensatedThreshold := tilt * threshold - varianceCoeff * varianceBudget
  let targetEvent := {ω : Ω |
    compensatedThreshold ≤ ∑ i ∈ Finset.range n, Z i ω}
  let sourceEvent := {ω : Ω |
    threshold ≤ ∑ i ∈ Finset.range n, Y i ω ∧
      (∑ i ∈ Finset.range n, V i ω) ≤ varianceBudget}
  have hreal := measure_sum_ge_le_of_hasCondMGFUpperBoundAt
    (μ := μ) (ℱ := ℱ) (Y := Z) (t := 1) (ψY := fun _ => 0)
      h_adapted h0 n h_mgf compensatedThreshold (by norm_num)
  have hreal' : μ.real targetEvent ≤
      Real.exp (-tilt * threshold + varianceCoeff * varianceBudget) := by
    simpa [Z, targetEvent, compensatedThreshold, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sub_eq_add_neg, add_comm] using hreal
  have htarget : μ targetEvent ≤
      ENNReal.ofReal (Real.exp
        (-tilt * threshold + varianceCoeff * varianceBudget)) := by
    rw [Measure.real] at hreal'
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top μ targetEvent) (Real.exp_pos _).le).2 hreal'
  have hsubset : sourceEvent ⊆ targetEvent := by
    intro ω hω
    change threshold ≤ ∑ i ∈ Finset.range n, Y i ω ∧
      (∑ i ∈ Finset.range n, V i ω) ≤ varianceBudget at hω
    change compensatedThreshold ≤
      ∑ i ∈ Finset.range n, Z i ω
    have hdeviation := mul_le_mul_of_nonneg_left hω.1 htilt
    have hvariance := mul_le_mul_of_nonneg_left hω.2 hvarianceCoeff
    simp only [Z, Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp only [compensatedThreshold]
    linarith
  change μ sourceEvent ≤ _
  exact (measure_mono hsubset).trans htarget

end BanditRLProof.Concentration
