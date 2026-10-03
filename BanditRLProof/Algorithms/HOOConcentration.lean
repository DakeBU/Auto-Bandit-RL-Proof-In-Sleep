import BanditRLProof.Algorithms.HOOConditionalMGF

/-! Count-dependent concentration for the actual chronological HOO trajectory,
including its first reward. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory

noncomputable def regionNoise (ν ρ : ℝ) (law : Kernel Node ℝ) (v : Node)
    (i : ℕ) (Y : ℕ → ℝ) : ℝ :=
  if v <+: action ν ρ Y i then Y i - nodeMean law (action ν ρ Y i) else 0

noncomputable def regionCount (ν ρ : ℝ) (v : Node) (i : ℕ) (Y : ℕ → ℝ) : ℝ :=
  if v <+: action ν ρ Y i then 1 else 0

theorem action_prefixExtension_at (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    action ν ρ (prefixExtension n (Preorder.frestrictLe n Y)) n = action ν ρ Y n := by
  apply action_causal
  intro i hi
  simp only [prefixExtension, dif_pos (show i ≤ n by omega), Preorder.frestrictLe_apply]

theorem measurable_action_piLE (ν ρ : ℝ) (n : ℕ) :
    Measurable[Filtration.piLE n] (fun Y : ℕ → ℝ => action ν ρ Y n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hr : Measurable[MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
      (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n) := Measurable.of_comap_le le_rfl
  have hm := ((measurable_action ν ρ n).comp (measurable_prefixExtension n)).comp hr
  simpa only [Function.comp_def, action_prefixExtension_at] using hm

theorem measurable_coordinate_piLE (n : ℕ) :
    Measurable[Filtration.piLE n] (fun Y : ℕ → ℝ => Y n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hr : Measurable[MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
      (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n) := Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ)
    (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)).comp hr

theorem region_compensated_adapted (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (tilt : ℝ) :
    StronglyAdapted Filtration.piLE (fun i Y =>
      tilt * regionNoise ν ρ law v i Y - tilt^2/8 * regionCount ν ρ v i Y) := by
  intro i
  have hn := measurable_action_piLE ν ρ i
  have hp : @MeasurableSet (ℕ → ℝ) (Filtration.piLE i)
      {Y | v <+: action ν ρ Y i} := hn (Set.to_countable {a : Node | v <+: a}).measurableSet
  have hy := measurable_coordinate_piLE i
  have hm := (measurable_of_countable (f := nodeMean law)).comp hn
  exact (((hy.sub hm).ite hp measurable_const).const_mul tilt |>.sub
    ((measurable_const.ite hp measurable_const).const_mul (tilt^2/8))).stronglyMeasurable

theorem region_compensated_successor (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (tilt : ℝ) :
    Concentration.HasCondMGFUpperBoundAt (Filtration.piLE n) (Filtration.piLE.le n)
      (fun Y => tilt * regionNoise ν ρ law v (n+1) Y -
        tilt^2/8 * regionCount ν ρ v (n+1) Y) 1 0 (trajectory ν ρ law) := by
  have h := trajectory_region_condMGF ν ρ law hbound v n tilt
  simpa only [Filtration.piLE_eq_comap_frestrictLe, regionCompensated,
    regionIncrement, regionSelected, selectedNode, action_prefixExtension,
    regionNoise, regionCount] using h

theorem region_compensated_initial (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (tilt : ℝ) :
    Concentration.HasMGFUpperBoundAt (fun Y => tilt * regionNoise ν ρ law v 0 Y -
      tilt^2/8 * regionCount ν ρ v 0 Y) 1 0 (trajectory ν ρ law) := by
  have hzero (Y : ℕ → ℝ) : action ν ρ Y 0 = action ν ρ (fun _ => 0) 0 := rfl
  by_cases hv : v <+: action ν ρ (fun _ => 0) 0
  · have h := (bounded_node_fixedMGF law hbound (action ν ρ (fun _ => 0) 0) tilt).compensated
    rw [← trajectory_initial_law ν ρ law] at h
    have hh := Concentration.HasMGFUpperBoundAt.of_map (μ' := trajectory ν ρ law)
      (measurable_pi_apply 0).aemeasurable h
    simpa only [regionNoise, regionCount, hzero, if_pos hv, mul_one] using hh
  · simp only [regionNoise, regionCount, hzero, if_neg hv, mul_zero, sub_zero]
    constructor
    · intro s
      simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℕ → ℝ => (1 : ℝ))
        (trajectory ν ρ law))
    · simp [mgf]

/-- A regional noise/count tail for the real HOO process. Both the initial and
conditional MGF obligations are derived from its bounded reward kernels. -/
theorem region_noise_count_tail (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (tilt threshold countBudget : ℝ) (htilt : 0 ≤ tilt) :
    (trajectory ν ρ law) {Y |
      threshold ≤ ∑ i ∈ Finset.range n, regionNoise ν ρ law v i Y ∧
      (∑ i ∈ Finset.range n, regionCount ν ρ v i Y) ≤ countBudget} ≤
      ENNReal.ofReal (Real.exp (-tilt * threshold + tilt^2/8 * countBudget)) := by
  apply Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
    (ℱ := Filtration.piLE) (h_adapted := region_compensated_adapted ν ρ law v tilt)
    (h0 := region_compensated_initial ν ρ law hbound v tilt)
  · intro i _
    exact region_compensated_successor ν ρ law hbound v i tilt
  · exact htilt
  · positivity

theorem sum_regionCount_eq_visits (ν ρ : ℝ) (v : Node) (n : ℕ) (Y : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, regionCount ν ρ v i Y) = (visits (history ν ρ Y n) v : ℝ) := by
  induction n with
  | zero => simp [history, visits]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, history, visits_step, Nat.cast_add]
    simp only [regionCount, action]
    split_ifs <;> simp

theorem sum_regionNoise_eq_rewardSum_sub_means (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (n : ℕ) (Y : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, regionNoise ν ρ law v i Y) =
      rewardSum (history ν ρ Y n) v -
        ∑ i ∈ Finset.range n, regionCount ν ρ v i Y * nodeMean law (action ν ρ Y i) := by
  induction n with
  | zero => simp [history, rewardSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, history, rewardSum_step, Finset.sum_range_succ]
    simp only [regionNoise, regionCount, action]
    split_ifs <;> simp <;> ring

theorem region_negative_noise_count_tail (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (tilt threshold countBudget : ℝ) (htilt : 0 ≤ tilt) :
    (trajectory ν ρ law) {Y |
      threshold ≤ -(∑ i ∈ Finset.range n, regionNoise ν ρ law v i Y) ∧
      (visits (history ν ρ Y n) v : ℝ) ≤ countBudget} ≤
      ENNReal.ofReal (Real.exp (-tilt * threshold + tilt^2/8 * countBudget)) := by
  have ha : StronglyAdapted Filtration.piLE (fun i Y =>
      tilt * (-regionNoise ν ρ law v i Y) - tilt^2/8 * regionCount ν ρ v i Y) := by
    simpa only [neg_mul, neg_sq, mul_neg] using region_compensated_adapted ν ρ law v (-tilt)
  have h0 : Concentration.HasMGFUpperBoundAt (fun Y =>
      tilt * (-regionNoise ν ρ law v 0 Y) - tilt^2/8 * regionCount ν ρ v 0 Y)
      1 0 (trajectory ν ρ law) := by
    simpa only [neg_mul, neg_sq, mul_neg] using region_compensated_initial ν ρ law hbound v (-tilt)
  have hc (i : ℕ) : Concentration.HasCondMGFUpperBoundAt
      (Filtration.piLE i) (Filtration.piLE.le i) (fun Y =>
        tilt * (-regionNoise ν ρ law v (i+1) Y) - tilt^2/8 * regionCount ν ρ v (i+1) Y)
      1 0 (trajectory ν ρ law) := by
    simpa only [neg_mul, neg_sq, mul_neg] using
      region_compensated_successor ν ρ law hbound v i (-tilt)
  have h := Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
    (ℱ := Filtration.piLE) (fun i Y => -regionNoise ν ρ law v i Y)
    (regionCount ν ρ v) n tilt (tilt^2/8) threshold countBudget ha h0
    (fun i _ => hc i) htilt (by positivity)
  simpa only [Finset.sum_neg_distrib, sum_regionCount_eq_visits] using h

/-- Optimized upper tail, retaining the actual regional visit count in the event. -/
theorem region_noise_visits_tail (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (threshold countBudget : ℝ)
    (hthreshold : 0 ≤ threshold) (hcount : 0 < countBudget) :
    (trajectory ν ρ law) {Y |
      threshold ≤ ∑ i ∈ Finset.range n, regionNoise ν ρ law v i Y ∧
      (visits (history ν ρ Y n) v : ℝ) ≤ countBudget} ≤
      ENNReal.ofReal (Real.exp (-2 * threshold^2 / countBudget)) := by
  have h := region_noise_count_tail ν ρ law hbound v n (4*threshold/countBudget)
    threshold countBudget (by positivity)
  have he : -(4*threshold/countBudget)*threshold + (4*threshold/countBudget)^2/8*countBudget =
      -2*threshold^2/countBudget := by field_simp; ring
  simpa only [he, sum_regionCount_eq_visits] using h

theorem region_negative_noise_visits_tail (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (threshold countBudget : ℝ)
    (hthreshold : 0 ≤ threshold) (hcount : 0 < countBudget) :
    (trajectory ν ρ law) {Y |
      threshold ≤ -(∑ i ∈ Finset.range n, regionNoise ν ρ law v i Y) ∧
      (visits (history ν ρ Y n) v : ℝ) ≤ countBudget} ≤
      ENNReal.ofReal (Real.exp (-2 * threshold^2 / countBudget)) := by
  have h := region_negative_noise_count_tail ν ρ law hbound v n (4*threshold/countBudget)
    threshold countBudget (by positivity)
  have he : -(4*threshold/countBudget)*threshold + (4*threshold/countBudget)^2/8*countBudget =
      -2*threshold^2/countBudget := by field_simp; ring
  simpa only [he] using h

end BanditRLProof.HOO
