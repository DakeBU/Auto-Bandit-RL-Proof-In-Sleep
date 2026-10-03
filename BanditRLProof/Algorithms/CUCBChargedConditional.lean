import BanditRLProof.Algorithms.CUCBChargedMGF
import Mathlib.Probability.Kernel.CondDistrib

/-! Conditional trigger factor along the actual history-dependent charging
recursion and actual randomized CUCB trajectory. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace ChargeData
variable {A : Type*} {m : ℕ} (C : ChargeData A m) [Nonempty A]

noncomputable def prefixActions (n : ℕ) (h : (i : Finset.Iic n) → Round A m) : ℕ → A :=
  fun t => if ht : t≤n then (h ⟨t, Finset.mem_Iic.mpr ht⟩).1 else Classical.choice inferInstance

noncomputable def prefixCounters (n : ℕ) (h : (i : Finset.Iic n) → Round A m) : Fin m → ℕ :=
  C.counters (prefixActions n h) (n+1)

theorem prefixCounters_eq (n : ℕ) (Y : ℕ → Round A m) :
    C.prefixCounters n (Preorder.frestrictLe n Y) = C.counters (fun t => (Y t).1) (n+1) := by
  apply C.counters_causal
  intro t ht
  simp only [prefixActions, dif_pos (show t≤n by omega), Preorder.frestrictLe_apply]

variable [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

omit [Countable A] [MeasurableSingletonClass A] in
theorem measurable_prefixActions (n : ℕ) : Measurable (prefixActions (A:=A) (m:=m) n) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t≤n
  · simp only [prefixActions, dif_pos ht]
    exact measurable_fst.comp (measurable_pi_apply _)
  · simp only [prefixActions, dif_neg ht]
    exact measurable_const

theorem measurable_prefixCounters (n : ℕ) : Measurable (C.prefixCounters n) :=
  (C.measurable_counters (n+1)).comp (measurable_prefixActions n)

variable [sA : StandardBorelSpace A]
variable (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
variable [IsMarkovKernel oracle] [IsMarkovKernel environment]
variable (i : Fin m) (htrigger : ∀a, i∈C.triggers a →
  C.triggerLower i≤(environment a (observedSet i)).toReal)
include htrigger sA

theorem cucb_condExp_chargedTriggerFactor (n : ℕ) (tilt : ℝ) (htilt : 0≤tilt) :
    (cucbTrajectory oracle environment)[fun Y =>
      C.chargedTriggerFactor i tilt (C.counters (fun t => (Y t).1) (n+1)) (Y (n+1)) |
      MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] ≤ᵐ[cucbTrajectory oracle environment]
        fun _ => 1 := by
  let P := fun Y : ℕ → Round A m => (Preorder.frestrictLe n Y, Y (n+1))
  have hP : Measurable P := (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1))
  letI : IsProbabilityMeasure ((cucbTrajectory oracle environment).map P) :=
    Measure.isProbabilityMeasure_map hP.aemeasurable
  have hi := C.integrable_chargedTriggerFactor_comp ((cucbTrajectory oracle environment).map P)
    i tilt (fun p => (C.prefixCounters n p.1,p.2))
      (((C.measurable_prefixCounters n).comp measurable_fst).prodMk measurable_snd)
  have hc := condExp_prod_ae_eq_integral_condDistrib' (μ:=cucbTrajectory oracle environment)
    (f:=fun p => C.chargedTriggerFactor i tilt (C.prefixCounters n p.1) p.2)
    (Preorder.measurable_frestrictLe n) (measurable_pi_apply (n+1)).aemeasurable hi
  simp only [prefixCounters_eq] at hc
  have hk := ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
    (cucbTrajectory_condDistrib oracle environment n)
  filter_upwards [hc, hk] with Y hc hk
  rw [hc, hk]
  simp only [cucbStepKernel, Kernel.comap_apply]
  exact C.roundKernel_chargedTriggerFactor_le_one oracle environment i htrigger _ _ tilt htilt

omit sA [Nonempty A] in
theorem cucb_initial_chargedTriggerFactor (tilt : ℝ) (htilt : 0≤tilt) :
    (∫Y, C.chargedTriggerFactor i tilt (C.counters (fun t => (Y t).1) 0) (Y 0)
      ∂cucbTrajectory oracle environment)≤1 := by
  have he := integral_map (μ:=cucbTrajectory oracle environment)
    (measurable_pi_apply 0).aemeasurable
    ((C.measurable_chargedTriggerFactor i tilt).comp
      (show Measurable (fun z : Round A m => ((fun _ => 0),z)) by fun_prop)).aestronglyMeasurable
  rw [cucbTrajectory_initial_law] at he
  simp only [Function.comp_def] at he
  change (∫Y, C.chargedTriggerFactor i tilt (fun _ => 0) (Y 0)
    ∂cucbTrajectory oracle environment)≤1
  rw [← he]
  exact C.roundKernel_chargedTriggerFactor_le_one oracle environment i htrigger _ _ tilt htilt

end ChargeData
end BanditRLProof.CUCB
