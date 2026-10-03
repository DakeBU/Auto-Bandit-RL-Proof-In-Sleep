import BanditRLProof.Algorithms.CUCBConditionalMGF

/-! Count-compensated concentration on the actual randomized CUCB path.
Both initial and conditional MGF premises are produced from its environment. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

variable {A : Type*} [MeasurableSpace A] {m : ℕ}

noncomputable def pathNoise (D : Measure UnitOutcome) (i : Fin m)
    (t : ℕ) (Y : ℕ → Round A m) : ℝ := observedNoise D i (Y t).2

def pathCount (i : Fin m) (t : ℕ) (Y : ℕ → Round A m) : ℝ := observedIndicator i (Y t).2

theorem measurable_round_piLE (n : ℕ) :
    Measurable[Filtration.piLE n] (fun Y : ℕ → Round A m => Y n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hr : Measurable[MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
      (Preorder.frestrictLe (π := fun _ : ℕ => Round A m) n) := Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (X := fun _ : Finset.Iic n => Round A m)
    (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)).comp hr

theorem path_compensated_adapted (D : Measure UnitOutcome) (i : Fin m) (tilt : ℝ) :
    StronglyAdapted Filtration.piLE (fun t (Y : ℕ → Round A m) =>
      tilt*pathNoise D i t Y-tilt^2/8*pathCount i t Y) := by
  intro t
  exact ((measurable_observedCompensated D i tilt).comp
    (measurable_snd.comp (measurable_round_piLE t))).stronglyMeasurable

variable [StandardBorelSpace A] [Nonempty A]
variable (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
variable [IsMarkovKernel oracle] [IsMarkovKernel environment]
variable (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m)
variable (hcompat : ∀a, ObservationCompatible (environment a) D i)
include hcompat

theorem path_noise_count_tail (n : ℕ) (tilt threshold budget : ℝ) (htilt : 0≤tilt) :
    (cucbTrajectory oracle environment) {Y |
      threshold≤∑t∈Finset.range n, pathNoise D i t Y ∧
      (∑t∈Finset.range n, pathCount i t Y)≤budget} ≤
    ENNReal.ofReal (Real.exp (-tilt*threshold+tilt^2/8*budget)) := by
  apply Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
    (ℱ:=Filtration.piLE) (h_adapted:=path_compensated_adapted D i tilt)
    (h0:=cucb_initial_MGF oracle environment D i hcompat tilt)
  · intro t ht
    simpa only [Filtration.piLE_eq_comap_frestrictLe, observedCompensated, pathNoise, pathCount]
      using cucb_successor_condMGF oracle environment D i hcompat t tilt
  · exact htilt
  · positivity

theorem path_noise_count_tail_optimized (n : ℕ) (threshold budget : ℝ)
    (hx : 0≤threshold) (hb : 0<budget) :
    (cucbTrajectory oracle environment) {Y |
      threshold≤∑t∈Finset.range n, pathNoise D i t Y ∧
      (∑t∈Finset.range n, pathCount i t Y)≤budget} ≤
    ENNReal.ofReal (Real.exp (-2*threshold^2/budget)) := by
  have h := path_noise_count_tail oracle environment D i hcompat n
    (4*threshold/budget) threshold budget (by positivity)
  have he : -(4*threshold/budget)*threshold+(4*threshold/budget)^2/8*budget =
      -2*threshold^2/budget := by field_simp; ring
  simpa only [he] using h

theorem path_negative_noise_count_tail (n : ℕ) (tilt threshold budget : ℝ) (htilt : 0≤tilt) :
    (cucbTrajectory oracle environment) {Y |
      threshold≤-(∑t∈Finset.range n, pathNoise D i t Y) ∧
      (∑t∈Finset.range n, pathCount i t Y)≤budget} ≤
    ENNReal.ofReal (Real.exp (-tilt*threshold+tilt^2/8*budget)) := by
  have ha : StronglyAdapted Filtration.piLE (fun t (Y : ℕ → Round A m) =>
      tilt*(-pathNoise D i t Y)-tilt^2/8*pathCount i t Y) := by
    simpa only [neg_mul, neg_sq, mul_neg] using path_compensated_adapted (A:=A) D i (-tilt)
  have h0 : Concentration.HasMGFUpperBoundAt (fun Y : ℕ → Round A m =>
      tilt*(-pathNoise D i 0 Y)-tilt^2/8*pathCount i 0 Y) 1 0
      (cucbTrajectory oracle environment) := by
    simpa only [observedCompensated, pathNoise, pathCount, neg_mul, neg_sq, mul_neg]
      using cucb_initial_MGF oracle environment D i hcompat (-tilt)
  have hc (t : ℕ) : Concentration.HasCondMGFUpperBoundAt (Filtration.piLE t)
      (Filtration.piLE.le t) (fun Y : ℕ → Round A m =>
        tilt*(-pathNoise D i (t+1) Y)-tilt^2/8*pathCount i (t+1) Y) 1 0
      (cucbTrajectory oracle environment) := by
    simpa only [Filtration.piLE_eq_comap_frestrictLe, observedCompensated,
      pathNoise, pathCount, neg_mul, neg_sq, mul_neg]
      using cucb_successor_condMGF oracle environment D i hcompat t (-tilt)
  have h := Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
    (ℱ:=Filtration.piLE) (fun t Y => -pathNoise D i t Y) (pathCount i) n tilt
    (tilt^2/8) threshold budget ha h0 (fun t _ => hc t) htilt (by positivity)
  simpa only [Finset.sum_neg_distrib] using h

theorem path_negative_noise_count_tail_optimized (n : ℕ) (threshold budget : ℝ)
    (hx : 0≤threshold) (hb : 0<budget) :
    (cucbTrajectory oracle environment) {Y |
      threshold≤-(∑t∈Finset.range n, pathNoise D i t Y) ∧
      (∑t∈Finset.range n, pathCount i t Y)≤budget} ≤
    ENNReal.ofReal (Real.exp (-2*threshold^2/budget)) := by
  have h := path_negative_noise_count_tail oracle environment D i hcompat n
    (4*threshold/budget) threshold budget (by positivity)
  have he : -(4*threshold/budget)*threshold+(4*threshold/budget)^2/8*budget =
      -2*threshold^2/budget := by field_simp; ring
  simpa only [he] using h

omit hcompat [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] in
theorem sum_pathCount (n : ℕ) (Y : ℕ → Round A m) :
    (∑t∈Finset.range n, pathCount i t Y) =
      (observationCount (fun t => (Y t).2) n i : ℝ) := by
  simp only [observationCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  cases hm : (Y t).2.1 i <;> simp [pathCount, observedIndicator, hm]

omit hcompat [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [IsProbabilityMeasure D] in
theorem sum_pathNoise (n : ℕ) (Y : ℕ → Round A m) :
    (∑t∈Finset.range n, pathNoise D i t Y) =
      observationSum (fun t => (Y t).2) n i -
        (observationCount (fun t => (Y t).2) n i : ℝ)*marginalMean D := by
  induction n with
  | zero => simp [observationSum, observationCount]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, observationSum_succ, observationCount_succ, Nat.cast_add]
    cases hm : (Y n).2.1 i with
    | false => simp [pathNoise, observedNoise, observation, hm]
    | true =>
      simp [pathNoise, observedNoise, observation, hm]
      ring

theorem observed_sum_upper_tail (n : ℕ) (threshold budget : ℝ)
    (hx : 0≤threshold) (hb : 0<budget) :
    (cucbTrajectory oracle environment) {Y |
      threshold≤observationSum (fun t => (Y t).2) n i -
        (observationCount (fun t => (Y t).2) n i : ℝ)*marginalMean D ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤budget} ≤
    ENNReal.ofReal (Real.exp (-2*threshold^2/budget)) := by
  simpa only [sum_pathNoise, sum_pathCount] using
    path_noise_count_tail_optimized oracle environment D i hcompat n threshold budget hx hb

theorem observed_sum_lower_tail (n : ℕ) (threshold budget : ℝ)
    (hx : 0≤threshold) (hb : 0<budget) :
    (cucbTrajectory oracle environment) {Y |
      threshold≤(observationCount (fun t => (Y t).2) n i : ℝ)*marginalMean D -
        observationSum (fun t => (Y t).2) n i ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤budget} ≤
    ENNReal.ofReal (Real.exp (-2*threshold^2/budget)) := by
  simpa only [sum_pathNoise, sum_pathCount, neg_sub] using
    path_negative_noise_count_tail_optimized oracle environment D i hcompat n threshold budget hx hb

end BanditRLProof.CUCB
