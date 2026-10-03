import BanditRLProof.Algorithms.CUCBRoundMGF
import BanditRLProof.ConcentrationConditionalMGF

/-! Conditional compensated MGF for the actual CUCB trajectory. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

noncomputable def observedNoise {m : ℕ} (D : Measure UnitOutcome) (i : Fin m)
    (z : Feedback m) : ℝ := if z.1 i then (z.2.1 i:ℝ)-marginalMean D else 0

def observedIndicator {m : ℕ} (i : Fin m) (z : Feedback m) : ℝ := if z.1 i then 1 else 0

noncomputable def observedCompensated {m : ℕ} (D : Measure UnitOutcome) (i : Fin m)
    (tilt : ℝ) (z : Feedback m) : ℝ :=
  tilt*observedNoise D i z-tilt^2/8*observedIndicator i z

theorem measurable_observedCompensated {m : ℕ} (D : Measure UnitOutcome) (i : Fin m)
    (tilt : ℝ) : Measurable (observedCompensated D i tilt) := by
  have hn : Measurable (observedNoise D i) := by
    unfold observedNoise
    exact (by fun_prop : Measurable (fun z : Feedback m => (z.2.1 i:ℝ)-marginalMean D)).ite
      (measurableSet_observedSet i) measurable_const
  have hc : Measurable (observedIndicator i) := by
    unfold observedIndicator
    exact measurable_const.ite (measurableSet_observedSet i) measurable_const
  exact (hn.const_mul tilt).sub (hc.const_mul (tilt^2/8))

theorem observedCompensated_abs_le {m : ℕ} (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (i : Fin m) (tilt : ℝ) (z : Feedback m) :
    |observedCompensated D i tilt z|≤|tilt|+tilt^2/8 := by
  have hm := marginalMean_mem D
  have hx : |(z.2.1 i:ℝ)-marginalMean D|≤1 :=
    abs_le.mpr ⟨by linarith [(z.2.1 i).property.1, hm.2],
      by linarith [(z.2.1 i).property.2, hm.1]⟩
  cases hz : z.1 i
  · simp [observedCompensated, observedNoise, observedIndicator, hz]
    positivity
  · simp only [observedCompensated, observedNoise, observedIndicator, hz, ↓reduceIte, mul_one]
    calc
      _ ≤ |tilt*((z.2.1 i:ℝ)-marginalMean D)|+|tilt^2/8| := abs_sub _ _
      _ = |tilt| * |(z.2.1 i:ℝ)-marginalMean D|+tilt^2/8 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0≤tilt^2/8)]
      _ ≤ _ := by nlinarith [abs_nonneg tilt]

theorem integrable_exp_observedCompensated {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {m : ℕ}
    (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m) (tilt scale : ℝ)
    (g : Ω → Feedback m) (hg : Measurable g) :
    Integrable (fun ω => Real.exp (scale*observedCompensated D i tilt (g ω))) ν := by
  apply (integrable_const (Real.exp (|scale| * (|tilt|+tilt^2/8)))).mono'
    (((measurable_observedCompensated D i tilt).comp hg).const_mul scale).exp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |scale*observedCompensated D i tilt (g ω)| := le_abs_self _
    _ = |scale| * |observedCompensated D i tilt (g ω)| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (observedCompensated_abs_le D i tilt (g ω)) (abs_nonneg _)

theorem exp_observedCompensated {m : ℕ} (D : Measure UnitOutcome) (i : Fin m)
    (tilt : ℝ) (z : Feedback m) :
    Real.exp (observedCompensated D i tilt z)=observedFactor D i tilt z :=
  (observedFactor_eq_exp D i tilt z).symm

variable {A : Type*} [MeasurableSpace A] [sA : StandardBorelSpace A] [neA : Nonempty A] {m : ℕ}
variable (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
variable [IsMarkovKernel oracle] [IsMarkovKernel environment]
variable (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m)
variable (hcompat : ∀a, ObservationCompatible (environment a) D i)
include hcompat sA neA

theorem cucb_condExp_observedCompensated (n : ℕ) (tilt : ℝ) :
    (cucbTrajectory oracle environment)[fun Y =>
      Real.exp (observedCompensated D i tilt (Y (n+1)).2) |
      MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] ≤ᵐ[cucbTrajectory oracle environment]
      fun _ => 1 := by
  let P := fun Y : ℕ → Round A m => (Preorder.frestrictLe n Y, Y (n+1))
  have hP : Measurable P := (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1))
  letI : IsProbabilityMeasure ((cucbTrajectory oracle environment).map P) :=
    Measure.isProbabilityMeasure_map hP.aemeasurable
  have hi := integrable_exp_observedCompensated ((cucbTrajectory oracle environment).map P)
    D i tilt 1 (fun p => p.2.2) (by fun_prop)
  simp only [one_mul] at hi
  have hc := condExp_prod_ae_eq_integral_condDistrib' (μ:=cucbTrajectory oracle environment)
    (f:=fun p => Real.exp (observedCompensated D i tilt p.2.2))
    (Preorder.measurable_frestrictLe n) (measurable_pi_apply (n+1)).aemeasurable hi
  have hk := ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
    (cucbTrajectory_condDistrib oracle environment n)
  filter_upwards [hc, hk] with Y hc hk
  rw [hc, hk]
  simp only [cucbStepKernel, Kernel.comap_apply, exp_observedCompensated]
  exact roundKernel_observedFactor_le_one oracle environment D i hcompat _ tilt

theorem cucb_successor_condMGF (n : ℕ) (tilt : ℝ) :
    Concentration.HasCondMGFUpperBoundAt
      (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
      (Preorder.measurable_frestrictLe n).comap_le
      (fun Y => observedCompensated D i tilt (Y (n+1)).2) 1 0
      (cucbTrajectory oracle environment) := by
  apply Concentration.hasCondMGFUpperBoundAt_of_condExp_le
  · intro scale
    exact integrable_exp_observedCompensated (cucbTrajectory oracle environment) D i tilt scale
      (fun Y => (Y (n+1)).2) (by fun_prop)
  · simpa only [one_mul, Real.exp_zero] using
      cucb_condExp_observedCompensated oracle environment D i hcompat n tilt

omit sA neA in
theorem cucb_initial_MGF (tilt : ℝ) :
    Concentration.HasMGFUpperBoundAt (fun Y : ℕ → Round A m =>
      observedCompensated D i tilt (Y 0).2) 1 0 (cucbTrajectory oracle environment) := by
  constructor
  · intro scale
    exact integrable_exp_observedCompensated (cucbTrajectory oracle environment) D i tilt scale
      (fun Y => (Y 0).2) (by fun_prop)
  · simp only [mgf, one_mul, Real.exp_zero, exp_observedCompensated]
    have he := integral_map (μ:=cucbTrajectory oracle environment)
      (measurable_pi_apply 0).aemeasurable
      ((measurable_observedFactor D i tilt).comp measurable_snd).aestronglyMeasurable
    rw [cucbTrajectory_initial_law] at he
    simp only [Function.comp_def] at he
    rw [← he]
    exact roundKernel_observedFactor_le_one oracle environment D i hcompat _ tilt

end BanditRLProof.CUCB
