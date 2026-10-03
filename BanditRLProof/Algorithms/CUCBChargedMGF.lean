import BanditRLProof.Algorithms.CUCBCharge
import BanditRLProof.Algorithms.CUCBTriggerMGF
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! The actual oracle mixture preserves the trigger bound for the normalized
charge, which is chosen before the environment draws the current feedback. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace ChargeData
variable {A : Type*} {m : ℕ} (C : ChargeData A m)

noncomputable def chargedTriggerFactor (i : Fin m) (tilt : ℝ)
    (N : Fin m → ℕ) (z : Round A m) : ℝ :=
  if C.choose N z.1=some i then triggerFactor i (C.triggerLower i) tilt z.2 else 1

theorem chargedTriggerFactor_nonneg (i : Fin m) (tilt : ℝ) (N : Fin m → ℕ) (z : Round A m) :
    0≤C.chargedTriggerFactor i tilt N z := by
  unfold chargedTriggerFactor
  split_ifs
  · exact triggerFactor_nonneg _ _ _ _
  · norm_num

theorem chargedTriggerFactor_le (i : Fin m) (tilt : ℝ) (N : Fin m → ℕ) (z : Round A m) :
    C.chargedTriggerFactor i tilt N z ≤
      Real.exp (|tilt|+|(1-Real.exp (-tilt))*C.triggerLower i|) := by
  unfold chargedTriggerFactor
  split_ifs
  · exact triggerFactor_le _ _ _ _
  · exact Real.one_le_exp (by positivity)

variable [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

theorem measurable_chargedTriggerFactor (i : Fin m) (tilt : ℝ) :
    Measurable (fun p : (Fin m → ℕ) × Round A m => C.chargedTriggerFactor i tilt p.1 p.2) := by
  unfold chargedTriggerFactor
  have hc := C.measurable_choose.comp
    (show Measurable (fun p : (Fin m → ℕ) × Round A m => (p.1,p.2.1)) by fun_prop)
  exact ((measurable_triggerFactor i (C.triggerLower i) tilt).comp (by fun_prop)).ite
    (hc (measurableSet_singleton (some i))) measurable_const

theorem integrable_chargedTriggerFactor_comp {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (i : Fin m) (tilt : ℝ)
    (g : Ω → (Fin m → ℕ) × Round A m) (hg : Measurable g) :
    Integrable (fun ω => C.chargedTriggerFactor i tilt (g ω).1 (g ω).2) ν := by
  apply (integrable_const (Real.exp (|tilt|+|(1-Real.exp (-tilt))*C.triggerLower i|))).mono'
    ((C.measurable_chargedTriggerFactor i tilt).comp hg).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (C.chargedTriggerFactor_nonneg _ _ _ _)]
  exact C.chargedTriggerFactor_le _ _ _ _

theorem roundKernel_chargedTriggerFactor_le_one
    (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
    [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (i : Fin m) (htrigger : ∀a, i∈C.triggers a →
      C.triggerLower i≤(environment a (observedSet i)).toReal)
    (v : Input m) (N : Fin m → ℕ) (tilt : ℝ) (htilt : 0≤tilt) :
    (∫z, C.chargedTriggerFactor i tilt N z ∂roundKernel oracle environment v)≤1 := by
  have hi := C.integrable_chargedTriggerFactor_comp (roundKernel oracle environment v)
    i tilt (fun z => (N,z)) (by fun_prop)
  change Integrable (fun z : Round A m => C.chargedTriggerFactor i tilt N z)
    ((oracle ⊗ₖ environment.comap Prod.snd measurable_snd) v) at hi
  rw [roundKernel, ProbabilityTheory.integral_compProd hi]
  have ha (a : A) : (∫z, C.chargedTriggerFactor i tilt N (a,z) ∂environment a)≤1 := by
    by_cases hc : C.choose N a=some i
    · simp only [chargedTriggerFactor, hc, if_true]
      exact integral_triggerFactor_le_one (environment a) i (C.triggerLower i) tilt
        (htrigger a (C.choose_mem N a i hc).2) htilt
    · simp [chargedTriggerFactor, hc]
  have h := integral_mono hi.integral_compProd (integrable_const (1:ℝ)) ha
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

end ChargeData
end BanditRLProof.CUCB
