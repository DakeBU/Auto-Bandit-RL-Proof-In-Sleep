import BanditRLProof.Algorithms.HOOTrajectory
import BanditRLProof.ConcentrationConditionalMGF

/-! Bounded-reward conditional MGF producers for the actual HOO step kernel.
Region selection depends on the observed prefix, never on the next reward. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable def nodeMean (law : Kernel Node ℝ) (v : Node) : ℝ := ∫ y, y ∂law v

theorem bounded_node_subgaussian (law : Kernel Node ℝ) [IsMarkovKernel law]
    (hbound : ∀ v, ∀ᵐ y ∂law v, y ∈ Set.Icc (0 : ℝ) 1) (v : Node) :
    HasSubgaussianMGF (fun y => y - nodeMean law v) (1/4 : ℝ≥0) (law v) := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := law v) (X := fun y : ℝ => y)
    measurable_id.aemeasurable (hbound v)
  norm_num at h
  exact h

/-- The new setting supplies the existing fixed-MGF interface from bounded
reward laws, rather than assuming a conditional confidence theorem. -/
theorem bounded_node_fixedMGF (law : Kernel Node ℝ) [IsMarkovKernel law]
    (hbound : ∀ v, ∀ᵐ y ∂law v, y ∈ Set.Icc (0 : ℝ) 1) (v : Node) (tilt : ℝ) :
    Concentration.HasMGFUpperBoundAt (fun y => y - nodeMean law v) tilt (tilt^2/8) (law v) := by
  have h := bounded_node_subgaussian law hbound v
  refine ⟨h.integrable_exp_mul, ?_⟩
  have he : (((1/4 : ℝ≥0) : ℝ) * tilt^2 / 2) = tilt^2/8 := by norm_num; ring
  simpa only [he] using h.mgf_le tilt

noncomputable def selectedNode (ν ρ : ℝ) (n : ℕ) (h : (i : Finset.Iic n) → ℝ) : Node :=
  action ν ρ (prefixExtension n h) (n+1)

noncomputable def regionIncrement (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (n : ℕ) (h : (i : Finset.Iic n) → ℝ) (y : ℝ) : ℝ :=
  if v <+: selectedNode ν ρ n h then y - nodeMean law (selectedNode ν ρ n h) else 0

noncomputable def regionSelected (ν ρ : ℝ) (v : Node) (n : ℕ)
    (h : (i : Finset.Iic n) → ℝ) : ℝ := if v <+: selectedNode ν ρ n h then 1 else 0

theorem region_step_fixedMGF (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (h : (i : Finset.Iic n) → ℝ) (tilt : ℝ) :
    Concentration.HasMGFUpperBoundAt (regionIncrement ν ρ law v n h) tilt
      (tilt^2/8 * regionSelected ν ρ v n h) (stepKernel ν ρ law n h) := by
  unfold regionIncrement regionSelected selectedNode
  by_cases hv : v <+: action ν ρ (prefixExtension n h) (n+1)
  · simpa only [if_pos hv, mul_one, stepKernel,
      Kernel.comap_apply, selectedNode] using
      bounded_node_fixedMGF law hbound (selectedNode ν ρ n h) tilt
  · simp only [if_neg hv, mul_zero]
    constructor
    · intro s
      simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (stepKernel ν ρ law n h))
    · simp [mgf]

/-- Predictable variance is paid only when this region is selected. This is the
one-step exponential process needed for count-dependent concentration. -/
theorem region_step_compensated_integral_le_one (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (h : (i : Finset.Iic n) → ℝ) (tilt : ℝ) :
    (∫ y, Real.exp (tilt * regionIncrement ν ρ law v n h y -
      tilt^2/8 * regionSelected ν ρ v n h) ∂stepKernel ν ρ law n h) ≤ 1 := by
  have hg := (region_step_fixedMGF ν ρ law hbound v n h tilt).mgf_le
  simp only [Real.exp_sub, integral_div]
  apply (div_le_one (Real.exp_pos _)).mpr
  exact hg

theorem measurable_selectedNode (ν ρ : ℝ) (n : ℕ) :
    Measurable (selectedNode ν ρ n) :=
  (measurable_action ν ρ (n+1)).comp (measurable_prefixExtension n)

theorem measurable_regionSelected (ν ρ : ℝ) (v : Node) (n : ℕ) :
    Measurable (regionSelected ν ρ v n) := by
  exact (measurable_of_countable (f := fun a : Node =>
    if v <+: a then (1 : ℝ) else 0)).comp (measurable_selectedNode ν ρ n)

theorem measurable_regionIncrement (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (n : ℕ) :
    Measurable (fun p : ((i : Finset.Iic n) → ℝ) × ℝ =>
      regionIncrement ν ρ law v n p.1 p.2) := by
  have hn : Measurable (fun p : ((i : Finset.Iic n) → ℝ) × ℝ =>
      selectedNode ν ρ n p.1) :=
    (measurable_selectedNode ν ρ n).comp measurable_fst
  have hp : MeasurableSet {p : ((i : Finset.Iic n) → ℝ) × ℝ |
      v <+: selectedNode ν ρ n p.1} :=
    hn (Set.to_countable {a : Node | v <+: a}).measurableSet
  exact (measurable_snd.sub ((measurable_of_countable (f := nodeMean law)).comp hn)).ite
    hp measurable_const

noncomputable def regionCompensated (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (n : ℕ) (tilt : ℝ) (p : ((i : Finset.Iic n) → ℝ) × ℝ) : ℝ :=
  tilt * regionIncrement ν ρ law v n p.1 p.2 -
    tilt^2/8 * regionSelected ν ρ v n p.1

theorem measurable_regionCompensated (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (n : ℕ) (tilt : ℝ) :
    Measurable (regionCompensated ν ρ law v n tilt) :=
  ((measurable_regionIncrement ν ρ law v n).const_mul tilt).sub
    (((measurable_regionSelected ν ρ v n).comp measurable_fst).const_mul (tilt^2/8))

/-- All exponential moments are integrable under the joint prefix/reward law.
This supplies the global integrability required by conditional MGF iteration. -/
theorem integrable_regionCompensated_exp (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (tilt s : ℝ)
    (μ : Measure ((i : Finset.Iic n) → ℝ)) [IsProbabilityMeasure μ] :
    Integrable (fun p => Real.exp (s * regionCompensated ν ρ law v n tilt p))
      (μ ⊗ₘ stepKernel ν ρ law n) := by
  have hm := ((measurable_regionCompensated ν ρ law v n tilt).const_mul s).exp
  apply (Measure.integrable_compProd_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun h =>
      (region_step_fixedMGF ν ρ law hbound v n h tilt).compensated.integrable_exp_mul s
  · have hi := hm.norm.stronglyMeasurable.integral_kernel_prod_right'
      (κ := stepKernel ν ρ law n)
    apply Integrable.mono' (integrable_const
      (Real.exp ((s*tilt)^2/8 + |s| * (tilt^2/8))) :
      Integrable (fun _ => Real.exp ((s*tilt)^2/8 + |s| * (tilt^2/8))) μ)
      hi.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro h
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [abs_of_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le))]
    have hg := (region_step_fixedMGF ν ρ law hbound v n h (s*tilt)).mgf_le
    simp only [mgf] at hg
    have he : (fun y => Real.exp (s * regionCompensated ν ρ law v n tilt (h,y))) =
        fun y => Real.exp ((s*tilt) * regionIncrement ν ρ law v n h y) *
          Real.exp (-s * (tilt^2/8 * regionSelected ν ρ v n h)) := by
      funext y
      rw [← Real.exp_add]
      congr 1
      unfold regionCompensated
      ring
    rw [he, integral_mul_const]
    calc
      _ ≤ Real.exp ((s*tilt)^2/8 * regionSelected ν ρ v n h) *
          Real.exp (-s * (tilt^2/8 * regionSelected ν ρ v n h)) :=
        mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        unfold regionSelected
        split_ifs
        · simp only [mul_one]
          have hs : -s ≤ |s| := neg_le_abs s
          nlinarith [sq_nonneg tilt]
        · simp only [mul_zero, add_zero]
          positivity

/-- The conditional exponential inequality holds for the actual constructed
trajectory and its observed prefix, without a supplied concentration premise. -/
theorem trajectory_region_condExp_le_one (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (tilt : ℝ) :
    (trajectory ν ρ law)[fun Y => Real.exp
      (regionCompensated ν ρ law v n tilt (Preorder.frestrictLe n Y, Y (n+1))) |
      MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] ≤ᵐ[trajectory ν ρ law]
      fun _ => 1 := by
  letI : IsProbabilityMeasure ((trajectory ν ρ law).map (Preorder.frestrictLe n)) :=
    Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe n).aemeasurable
  have hi := integrable_regionCompensated_exp ν ρ law hbound v n tilt 1
    ((trajectory ν ρ law).map (Preorder.frestrictLe n))
  rw [trajectory_prefix_compProd] at hi
  simp only [one_mul] at hi
  have hc := condExp_prod_ae_eq_integral_condDistrib' (μ := trajectory ν ρ law)
    (f := fun p => Real.exp (regionCompensated ν ρ law v n tilt p))
    (Preorder.measurable_frestrictLe n)
    (measurable_pi_apply (n+1)).aemeasurable hi
  have hk := ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
    (trajectory_condDistrib ν ρ law n)
  filter_upwards [hc, hk] with Y hc hk
  rw [hc, hk]
  exact region_step_compensated_integral_le_one ν ρ law hbound v n
    (Preorder.frestrictLe n Y) tilt

/-- Actual HOO successor increments now inhabit the shared conditional MGF
interface. The only probabilistic premise is bounded support of each reward law. -/
theorem trajectory_region_condMGF (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (tilt : ℝ) :
    Concentration.HasCondMGFUpperBoundAt
      (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
      (Preorder.measurable_frestrictLe n).comap_le
      (fun Y => regionCompensated ν ρ law v n tilt
        (Preorder.frestrictLe n Y, Y (n+1))) 1 0 (trajectory ν ρ law) := by
  apply Concentration.hasCondMGFUpperBoundAt_of_condExp_le
  · intro s
    letI : IsProbabilityMeasure ((trajectory ν ρ law).map (Preorder.frestrictLe n)) :=
      Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe n).aemeasurable
    have hi := integrable_regionCompensated_exp ν ρ law hbound v n tilt s
      ((trajectory ν ρ law).map (Preorder.frestrictLe n))
    rw [trajectory_prefix_compProd] at hi
    exact (integrable_map_measure hi.aestronglyMeasurable
      ((Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1))).aemeasurable).mp hi
  · simpa only [one_mul, Real.exp_zero] using
      trajectory_region_condExp_le_one ν ρ law hbound v n tilt

end BanditRLProof.HOO
