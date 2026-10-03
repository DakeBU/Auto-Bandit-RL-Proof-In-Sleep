import BanditRLProof.Algorithms.CUCBTrajectory
import Mathlib.Probability.Moments.SubGaussian

/-! Bounded-outcome MGF produced from the primitive uncensored marginal law.
The current random observation mask remains inside the exponent. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

noncomputable def marginalMean (D : Measure UnitOutcome) : ℝ := ∫ x, (x:ℝ) ∂D

noncomputable def centeredFactor (D : Measure UnitOutcome) (tilt : ℝ) (x : UnitOutcome) : ℝ :=
  Real.exp (tilt*((x:ℝ)-marginalMean D)-tilt^2/8)

theorem measurable_centeredFactor (D : Measure UnitOutcome) (tilt : ℝ) :
    Measurable (centeredFactor D tilt) := by
  unfold centeredFactor
  fun_prop

theorem marginal_subgaussian (D : Measure UnitOutcome) [IsProbabilityMeasure D] :
    HasSubgaussianMGF (fun x : UnitOutcome => (x:ℝ)-marginalMean D) (1/4:ℝ≥0) D := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ:=D) (X:=fun x : UnitOutcome => (x:ℝ))
    measurable_subtype_coe.aemeasurable (Filter.Eventually.of_forall (fun x => x.property))
  norm_num at h
  exact h

theorem integrable_centeredFactor (D : Measure UnitOutcome) [IsProbabilityMeasure D] (tilt : ℝ) :
    Integrable (centeredFactor D tilt) D := by
  unfold centeredFactor
  simpa only [Real.exp_sub] using
    ((marginal_subgaussian D).integrable_exp_mul tilt).div_const (Real.exp (tilt^2/8))

theorem integral_centeredFactor_le_one (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (tilt : ℝ) : (∫ x, centeredFactor D tilt x ∂D)≤1 := by
  simp only [centeredFactor, Real.exp_sub, integral_div]
  apply (div_le_one (Real.exp_pos _)).2
  have h := (marginal_subgaussian D).mgf_le tilt
  have he : (((1/4:ℝ≥0):ℝ)*tilt^2/2)=tilt^2/8 := by norm_num; ring
  simpa only [mgf, he] using h

def observedSet {m : ℕ} (i : Fin m) : Set (Feedback m) := {z | z.1 i=true}

theorem measurableSet_observedSet {m : ℕ} (i : Fin m) : MeasurableSet (observedSet i) :=
  (by fun_prop : Measurable (fun z : Feedback m => z.1 i)) (measurableSet_singleton true)

/-- Primitive equality of measures, expressing the unchanged marginal law
upon observation. It is not a concentration or MGF assumption. -/
def ObservationCompatible {m : ℕ} (ν : Measure (Feedback m)) (D : Measure UnitOutcome)
    (i : Fin m) : Prop :=
  (ν.restrict (observedSet i)).map (fun z => z.2.1 i) = ν (observedSet i) • D

theorem observed_centeredFactor_integrable {m : ℕ} (ν : Measure (Feedback m))
    [IsProbabilityMeasure ν] (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (i : Fin m) (h : ObservationCompatible ν D i) (tilt : ℝ) :
    IntegrableOn (fun z => centeredFactor D tilt (z.2.1 i)) (observedSet i) ν := by
  have hf : Integrable (centeredFactor D tilt)
      ((ν.restrict (observedSet i)).map (fun z => z.2.1 i)) := by
    rw [h]
    exact (integrable_centeredFactor D tilt).smul_measure (measure_ne_top _ _)
  exact (integrable_map_measure (measurable_centeredFactor D tilt).aestronglyMeasurable
    (by fun_prop : Measurable (fun z : Feedback m => z.2.1 i)).aemeasurable).1 hf

theorem observed_centeredFactor_integral {m : ℕ} (ν : Measure (Feedback m))
    [IsProbabilityMeasure ν] (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (i : Fin m) (h : ObservationCompatible ν D i) (tilt : ℝ) :
    (∫ z in observedSet i, centeredFactor D tilt (z.2.1 i) ∂ν) =
      (ν (observedSet i)).toReal * ∫ x, centeredFactor D tilt x ∂D := by
  rw [← integral_map (by fun_prop : Measurable (fun z : Feedback m => z.2.1 i)).aemeasurable
    (measurable_centeredFactor D tilt).aestronglyMeasurable, h, integral_smul_measure]
  rfl

noncomputable def observedFactor {m : ℕ} (D : Measure UnitOutcome) (i : Fin m)
    (tilt : ℝ) (z : Feedback m) : ℝ :=
  if z.1 i then centeredFactor D tilt (z.2.1 i) else 1

theorem observedFactor_eq_piecewise {m : ℕ} (D : Measure UnitOutcome) (i : Fin m) (tilt : ℝ)
    [DecidablePred (· ∈ observedSet i)] :
    observedFactor D i tilt = (observedSet i).piecewise
      (fun z => centeredFactor D tilt (z.2.1 i)) (fun _ => 1) := by
  classical
  funext z
  by_cases hz : z.1 i=true <;> simp [observedFactor, Set.piecewise, observedSet, hz]

theorem observedFactor_eq_exp {m : ℕ} (D : Measure UnitOutcome) (i : Fin m)
    (tilt : ℝ) (z : Feedback m) :
    observedFactor D i tilt z = Real.exp
      (tilt * (if z.1 i then (z.2.1 i:ℝ)-marginalMean D else 0) -
        tilt^2/8 * (if z.1 i then 1 else 0)) := by
  cases hm : z.1 i <;> simp [observedFactor, centeredFactor, hm]

theorem integrable_observedFactor {m : ℕ} (ν : Measure (Feedback m))
    [IsProbabilityMeasure ν] (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (i : Fin m) (h : ObservationCompatible ν D i) (tilt : ℝ) :
    Integrable (observedFactor D i tilt) ν := by
  classical
  rw [observedFactor_eq_piecewise, ← Set.indicator_add_compl_eq_piecewise]
  exact ((observed_centeredFactor_integrable ν D i h tilt).integrable_indicator
    (measurableSet_observedSet i)).add
      ((integrable_const (1:ℝ)).integrableOn.integrable_indicator
        (measurableSet_observedSet i).compl)

theorem integral_observedFactor_le_one {m : ℕ} (ν : Measure (Feedback m))
    [IsProbabilityMeasure ν] (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (i : Fin m) (h : ObservationCompatible ν D i) (tilt : ℝ) :
    (∫ z, observedFactor D i tilt z ∂ν)≤1 := by
  classical
  rw [observedFactor_eq_piecewise, integral_piecewise (measurableSet_observedSet i)
    (observed_centeredFactor_integrable ν D i h tilt) (integrable_const (1:ℝ)),
    observed_centeredFactor_integral ν D i h tilt]
  have hbound := mul_le_mul_of_nonneg_left (integral_centeredFactor_le_one D tilt)
    (ENNReal.toReal_nonneg (a:=ν (observedSet i)))
  have htotal := measureReal_add_measureReal_compl (μ:=ν) (measurableSet_observedSet i)
  simp only [integral_const, smul_eq_mul, mul_one] at *
  simpa only [measureReal_def, Measure.restrict_apply_univ, measure_univ, ENNReal.toReal_one] using
    (calc (ν (observedSet i)).toReal * (∫ x, centeredFactor D tilt x ∂D) +
          (ν ((observedSet i)ᶜ)).toReal ≤
        (ν (observedSet i)).toReal + (ν ((observedSet i)ᶜ)).toReal := add_le_add hbound le_rfl
      _ = 1 := by simpa [measureReal_def] using htotal)

end BanditRLProof.CUCB
