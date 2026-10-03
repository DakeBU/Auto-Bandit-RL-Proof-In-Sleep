import BanditRLProof.Algorithms.CUCBObservationMGF
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Integrating the primitive masked MGF over the actual oracle action.
The action and its triggered feedback retain their joint round kernel. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem marginalMean_mem (D : Measure UnitOutcome) [IsProbabilityMeasure D] :
    marginalMean D ∈ Set.Icc (0:ℝ) 1 := by
  have hi : Integrable (fun x : UnitOutcome => (x:ℝ)) D :=
    (integrable_const (1:ℝ)).mono' measurable_subtype_coe.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg x.property.1] using x.property.2))
  refine ⟨integral_nonneg (fun x => x.property.1), ?_⟩
  have h := integral_mono hi (integrable_const (1:ℝ)) (fun x => x.property.2)
  simpa [marginalMean] using h

theorem centeredFactor_nonneg (D : Measure UnitOutcome) (tilt : ℝ) (x : UnitOutcome) :
    0≤centeredFactor D tilt x := (Real.exp_pos _).le

theorem centeredFactor_le (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (tilt : ℝ) (x : UnitOutcome) : centeredFactor D tilt x ≤ Real.exp |tilt| := by
  have hm := marginalMean_mem D
  have hx : |(x:ℝ)-marginalMean D|≤1 := abs_le.mpr ⟨by linarith [x.property.1, hm.2], by linarith [x.property.2, hm.1]⟩
  apply Real.exp_le_exp.mpr
  calc
    tilt*((x:ℝ)-marginalMean D)-tilt^2/8 ≤ tilt*((x:ℝ)-marginalMean D) := by nlinarith [sq_nonneg tilt]
    _ ≤ |tilt*((x:ℝ)-marginalMean D)| := le_abs_self _
    _ = |tilt| * |(x:ℝ)-marginalMean D| := abs_mul _ _
    _ ≤ |tilt| := by nlinarith [abs_nonneg tilt]

theorem observedFactor_nonneg {m : ℕ} (D : Measure UnitOutcome) (i : Fin m)
    (tilt : ℝ) (z : Feedback m) : 0≤observedFactor D i tilt z := by
  unfold observedFactor
  split_ifs
  · exact centeredFactor_nonneg D tilt _
  · norm_num

theorem observedFactor_le {m : ℕ} (D : Measure UnitOutcome) [IsProbabilityMeasure D]
    (i : Fin m) (tilt : ℝ) (z : Feedback m) : observedFactor D i tilt z≤Real.exp |tilt| := by
  unfold observedFactor
  split_ifs
  · exact centeredFactor_le D tilt _
  · exact Real.one_le_exp (abs_nonneg _)

theorem measurable_observedFactor {m : ℕ} (D : Measure UnitOutcome) (i : Fin m) (tilt : ℝ) :
    Measurable (observedFactor D i tilt) := by
  unfold observedFactor
  exact ((measurable_centeredFactor D tilt).comp (by fun_prop)).ite
    (measurableSet_observedSet i) measurable_const

theorem integrable_observedFactor_comp {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {m : ℕ}
    (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m) (tilt : ℝ)
    (g : Ω → Feedback m) (hg : Measurable g) :
    Integrable (fun ω => observedFactor D i tilt (g ω)) ν :=
  (integrable_const (Real.exp |tilt|)).mono'
    ((measurable_observedFactor D i tilt).comp hg).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (observedFactor_nonneg D i tilt (g ω))]
        using observedFactor_le D i tilt (g ω)))

theorem roundKernel_observedFactor_le_one {A : Type*} [MeasurableSpace A] {m : ℕ}
    (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
    [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m)
    (hcompat : ∀a, ObservationCompatible (environment a) D i) (v : Input m) (tilt : ℝ) :
    (∫ z, observedFactor D i tilt z.2 ∂roundKernel oracle environment v)≤1 := by
  have hi := integrable_observedFactor_comp (roundKernel oracle environment v) D i tilt
    Prod.snd measurable_snd
  change Integrable (fun z : Round A m => observedFactor D i tilt z.2)
    ((oracle ⊗ₖ environment.comap Prod.snd measurable_snd) v) at hi
  rw [roundKernel, ProbabilityTheory.integral_compProd hi]
  have h := integral_mono hi.integral_compProd (integrable_const (1:ℝ))
    (fun a => integral_observedFactor_le_one (environment a) D i (hcompat a) tilt)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

end BanditRLProof.CUCB
