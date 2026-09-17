import BanditRLProof.Algorithms.CUCBConfidence

/-! The clipped empirical-mean confidence event on the actual CUCB path.
The history length is `n`; the source decision round is `n+1`. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

noncomputable def confidenceRadius {m : ℕ} (Y : ℕ → Feedback m)
    (n : ℕ) (i : Fin m) (L : ℝ) : ℝ :=
  if observationCount Y n i = 0 then 1
  else min (Real.sqrt (L/(2*observationCount Y n i))) 1

theorem measurable_confidenceRadius {m : ℕ} (n : ℕ) (i : Fin m) (L : ℝ) :
    Measurable (fun Y : ℕ → Feedback m => confidenceRadius Y n i L) := by
  unfold confidenceRadius
  apply measurable_const.ite ((measurable_observationCount n i) (measurableSet_singleton 0))
  exact (measurable_const.div
    (measurable_const.mul (measurable_observationCount_real n i))).sqrt.min measurable_const

theorem count_mul_radius (T L : ℝ) (hT : 0<T) (hL : 0≤L) :
    T*Real.sqrt (L/(2*T)) = Real.sqrt (T*L/2) := by
  have hs := Real.sq_sqrt (show 0≤L/(2*T) by positivity)
  have ht := Real.sq_sqrt (show 0≤T*L/2 by positivity)
  have he : (T*Real.sqrt (L/(2*T)))^2 = T*L/2 := by
    rw [mul_pow, hs]
    field_simp
  nlinarith [Real.sqrt_nonneg (T*L/2),
    mul_nonneg hT.le (Real.sqrt_nonneg (L/(2*T)))]

theorem empirical_bad_implies_deviation {A : Type*} {m : ℕ}
    (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m)
    (n : ℕ) (L : ℝ) (hL : 0≤L) (Y : ℕ → Round A m)
    (hbad : confidenceRadius (fun t => (Y t).2) n i L <
      |empiricalMean (fun t => (Y t).2) n i-marginalMean D|) :
    ∃ lower : Bool, 0<observationCount (fun t => (Y t).2) n i ∧
      Real.sqrt ((observationCount (fun t => (Y t).2) n i : ℝ)*L/2) ≤
        pathDeviation D i n lower Y := by
  let Z := fun t => (Y t).2
  have hm := marginalMean_mem D
  have he0 := empiricalMean_nonneg Z n i
  have he1 := empiricalMean_le_one Z n i
  have hab : |empiricalMean Z n i-marginalMean D|≤1 :=
    abs_le.mpr ⟨by linarith [hm.2], by linarith [hm.1]⟩
  have hn : observationCount Z n i ≠ 0 := by
    intro hz
    change confidenceRadius Z n i L < _ at hbad
    simp only [confidenceRadius, hz, if_pos] at hbad
    exact (not_lt_of_ge hab) hbad
  have hT : (0:ℝ)<observationCount Z n i := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hr : Real.sqrt (L/(2*observationCount Z n i)) <
      |empiricalMean Z n i-marginalMean D| := by
    change (if observationCount Z n i=0 then 1 else _) < _ at hbad
    rw [if_neg hn, min_lt_iff] at hbad
    exact hbad.resolve_right (not_lt_of_ge hab)
  have hsum : (observationCount Z n i : ℝ)*
      (empiricalMean Z n i-marginalMean D) =
      observationSum Z n i-(observationCount Z n i : ℝ)*marginalMean D := by
    rw [empiricalMean, if_neg hn]
    field_simp
  rcases lt_abs.mp hr with h | h
  · refine ⟨false, Nat.pos_of_ne_zero hn, ?_⟩
    have hp := mul_lt_mul_of_pos_left h hT
    rw [count_mul_radius _ _ hT hL, hsum] at hp
    simpa only [pathDeviation, Bool.false_eq_true, if_false, sum_pathNoise] using hp.le
  · refine ⟨true, Nat.pos_of_ne_zero hn, ?_⟩
    have hp := mul_lt_mul_of_pos_left h hT
    rw [count_mul_radius _ _ hT hL, mul_neg, hsum] at hp
    simpa only [pathDeviation, if_true, sum_pathNoise] using hp.le

/-- On the source confidence event the clipped index is optimistic, and its
excess above the true mean is at most twice the clipped confidence radius. -/
theorem upperIndex_of_confidence {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1)
    (hgood : |empiricalMean Y n i-μ| ≤
      confidenceRadius Y n i (3*Real.log ((n:ℝ)+1))) :
    μ ≤ upperIndex Y n i ∧ upperIndex Y n i ≤
      μ+2*confidenceRadius Y n i (3*Real.log ((n:ℝ)+1)) := by
  by_cases hz : observationCount Y n i=0
  · simp only [upperIndex, confidenceRadius, hz, if_pos]
    exact ⟨hμ.2, by linarith [hμ.1]⟩
  · simp only [upperIndex, confidenceRadius, hz, ↓reduceIte] at hgood ⊢
    have hlo := (abs_le.mp hgood).1
    have hhi := (abs_le.mp hgood).2
    constructor
    · apply le_min
      · have hr := min_le_left (Real.sqrt (3*Real.log ((n:ℝ)+1)/
            (2*observationCount Y n i))) 1
        linarith
      · exact hμ.2
    · by_cases hs : Real.sqrt (3*Real.log ((n:ℝ)+1)/
          (2*observationCount Y n i)) ≤ 1
      · rw [min_eq_left hs] at hhi ⊢
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right (le_of_not_ge hs)]
        exact (min_le_right _ _).trans (by linarith [hμ.1])

variable {A : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] {m : ℕ}
variable (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
variable [IsMarkovKernel oracle] [IsMarkovKernel environment]
variable (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m)
variable (hcompat : ∀a, ObservationCompatible (environment a) D i)
include hcompat

theorem empirical_bad_probability (n : ℕ) (L : ℝ) (hL : 0≤L) :
    (cucbTrajectory oracle environment) {Y |
      confidenceRadius (fun t => (Y t).2) n i L <
        |empiricalMean (fun t => (Y t).2) n i-marginalMean D|} ≤
      2*(n:ENNReal)*ENNReal.ofReal (Real.exp (-L)) := by
  let E : Bool → Set (ℕ → Round A m) := fun lower => {Y |
    0<observationCount (fun t => (Y t).2) n i ∧
      Real.sqrt ((observationCount (fun t => (Y t).2) n i : ℝ)*L/2)≤
        pathDeviation D i n lower Y}
  have hs : {Y : ℕ → Round A m |
      confidenceRadius (fun t => (Y t).2) n i L <
        |empiricalMean (fun t => (Y t).2) n i-marginalMean D|} ⊆ E false ∪ E true := by
    intro Y hY
    obtain ⟨lower, hlower⟩ := empirical_bad_implies_deviation D i n L hL Y hY
    cases lower
    · exact Or.inl hlower
    · exact Or.inr hlower
  calc
    _ ≤ (cucbTrajectory oracle environment) (E false ∪ E true) := measure_mono hs
    _ ≤ (cucbTrajectory oracle environment) (E false) +
        (cucbTrajectory oracle environment) (E true) := measure_union_le _ _
    _ ≤ (n:ENNReal)*ENNReal.ofReal (Real.exp (-L)) +
        (n:ENNReal)*ENNReal.ofReal (Real.exp (-L)) :=
      add_le_add (path_deviation_confidence oracle environment D i hcompat n false L hL)
        (path_deviation_confidence oracle environment D i hcompat n true L hL)
    _ = _ := by ring

omit hcompat in
theorem round_confidence_arithmetic (n : ℕ) :
    2*(n:ℝ)*Real.exp (-(3*Real.log ((n:ℝ)+1))) ≤ 2/((n:ℝ)+1)^2 := by
  have ht : (0:ℝ)<(n:ℝ)+1 := by positivity
  have he : Real.exp (3*Real.log ((n:ℝ)+1)) = ((n:ℝ)+1)^3 := by
    rw [show (3:ℝ)=((3:ℕ):ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log ht]
  rw [Real.exp_neg, he]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  field_simp
  nlinarith [sq_nonneg (n:ℝ)]

theorem empirical_bad_probability_source (n : ℕ) :
    (cucbTrajectory oracle environment) {Y |
      confidenceRadius (fun t => (Y t).2) n i (3*Real.log ((n:ℝ)+1)) <
        |empiricalMean (fun t => (Y t).2) n i-marginalMean D|} ≤
      ENNReal.ofReal (2/((n:ℝ)+1)^2) := by
  have hL : 0≤3*Real.log ((n:ℝ)+1) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  calc
    _ ≤ 2*(n:ENNReal)*ENNReal.ofReal (Real.exp (-(3*Real.log ((n:ℝ)+1)))) :=
      empirical_bad_probability oracle environment D i hcompat n _ hL
    _ = ENNReal.ofReal (2*(n:ℝ)*Real.exp (-(3*Real.log ((n:ℝ)+1)))) := by
      simp [ENNReal.ofReal_mul]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (round_confidence_arithmetic n)

omit hcompat in
/-- Source nice event, before round `n+1`, simultaneously over all arms. -/
def NiceEvent (means : Fin m → ℝ) (n : ℕ) : Set (ℕ → Round A m) :=
  {Y | ∀i, |empiricalMean (fun t => (Y t).2) n i-means i| ≤
    confidenceRadius (fun t => (Y t).2) n i (3*Real.log ((n:ℝ)+1))}

omit hcompat [StandardBorelSpace A] [Nonempty A] in
theorem measurableSet_niceEvent (means : Fin m → ℝ) (n : ℕ) :
    MeasurableSet (NiceEvent (A:=A) means n) := by
  unfold NiceEvent
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hz : Measurable (fun Y : ℕ → Round A m => fun t => (Y t).2) := by fun_prop
  exact measurableSet_le
    (((measurable_empiricalMean n i).comp hz).sub measurable_const).abs
    ((measurable_confidenceRadius n i _).comp hz)
omit hcompat in
theorem niceEvent_complement_probability (laws : Fin m → Measure UnitOutcome)
    [∀i, IsProbabilityMeasure (laws i)]
    (hcompatAll : ∀a i, ObservationCompatible (environment a) (laws i) i) (n : ℕ) :
    (cucbTrajectory oracle environment) (NiceEvent (fun i => marginalMean (laws i)) n)ᶜ ≤
      ENNReal.ofReal (2*(m:ℝ)/((n:ℝ)+1)^2) := by
  let E : Fin m → Set (ℕ → Round A m) := fun i => {Y |
    confidenceRadius (fun t => (Y t).2) n i (3*Real.log ((n:ℝ)+1)) <
      |empiricalMean (fun t => (Y t).2) n i-marginalMean (laws i)|}
  have hs : (NiceEvent (fun i => marginalMean (laws i)) n)ᶜ ⊆
      ⋃i∈(Finset.univ : Finset (Fin m)), E i := by
    intro Y hY
    simp only [NiceEvent, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hY
    obtain ⟨i, hi⟩ := hY
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hi⟩⟩
  calc
    _ ≤ (cucbTrajectory oracle environment) (⋃i∈(Finset.univ : Finset (Fin m)), E i) :=
      measure_mono hs
    _ ≤ ∑i:Fin m, (cucbTrajectory oracle environment) (E i) :=
      ProbabilityUnionBound.measure_biUnion_finset_le _ _ E
    _ ≤ ∑_i:Fin m, ENNReal.ofReal (2/((n:ℝ)+1)^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact empirical_bad_probability_source oracle environment (laws i) i
        (fun a => hcompatAll a i) n
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
      congr 1
      ring

end BanditRLProof.CUCB

