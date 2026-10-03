import BanditRLProof.Algorithms.CUCBChargedConditional
import BanditRLProof.Algorithms.CUCBConcentration
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Accumulating charged-trigger exponential bounds on the actual CUCB path. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace ChargeData
variable {A : Type*} {m : ℕ} (C : ChargeData A m)

noncomputable def chargeValue (i : Fin m) (N : Fin m → ℕ) (z : Round A m) : ℝ :=
  if C.choose N z.1=some i then 1 else 0

noncomputable def successValue (i : Fin m) (N : Fin m → ℕ) (z : Round A m) : ℝ :=
  if C.choose N z.1=some i ∧ z.2.1 i=true then 1 else 0

noncomputable def compensation (i : Fin m) (tilt : ℝ) (N : Fin m → ℕ) (z : Round A m) : ℝ :=
  (1-Real.exp (-tilt))*C.triggerLower i*C.chargeValue i N z-tilt*C.successValue i N z

theorem exp_compensation (i : Fin m) (tilt : ℝ) (N : Fin m → ℕ) (z : Round A m) :
    Real.exp (C.compensation i tilt N z)=C.chargedTriggerFactor i tilt N z := by
  by_cases hc : C.choose N z.1=some i
  · cases hz : z.2.1 i <;>
      simp [compensation, chargeValue, successValue, chargedTriggerFactor, triggerFactor, hc, hz,
        sub_eq_add_neg, add_comm]
  · simp [compensation, chargeValue, successValue, chargedTriggerFactor, hc]

theorem compensation_abs_le (i : Fin m) (tilt : ℝ) (N : Fin m → ℕ) (z : Round A m) :
    |C.compensation i tilt N z|≤|(1-Real.exp (-tilt))*C.triggerLower i|+|tilt| := by
  by_cases hc : C.choose N z.1=some i
  · cases hz : z.2.1 i
    · simp [compensation, chargeValue, successValue, hc, hz]
    · simpa [compensation, chargeValue, successValue, hc, hz] using
        abs_sub ((1-Real.exp (-tilt))*C.triggerLower i) tilt
  · simp only [compensation, chargeValue, successValue, hc, false_and, if_false, mul_zero, sub_self, abs_zero]
    positivity

theorem sum_chargeValue (actions : ℕ → Round A m) (n : ℕ) (i : Fin m) :
    (∑t∈Finset.range n, C.chargeValue i (C.counters (fun s => (actions s).1) t) (actions t)) =
      (C.counters (fun t => (actions t).1) n i : ℝ) := by
  rw [counters_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  unfold chargeValue
  split_ifs <;> simp

theorem sum_successValue (Y : ℕ → Round A m) (n : ℕ) (i : Fin m) :
    (∑t∈Finset.range n, C.successValue i (C.counters (fun s => (Y s).1) t) (Y t)) =
      (C.chargedObservations Y n i : ℝ) := by
  unfold chargedObservations
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  unfold successValue
  split_ifs <;> simp

variable [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

theorem measurable_compensation (i : Fin m) (tilt : ℝ) :
    Measurable (fun p : (Fin m → ℕ) × Round A m => C.compensation i tilt p.1 p.2) := by
  have hc := C.measurable_choose.comp
    (show Measurable (fun p : (Fin m → ℕ) × Round A m => (p.1,p.2.1)) by fun_prop)
  have hs := hc (measurableSet_singleton (some i))
  have ho : MeasurableSet {p : (Fin m → ℕ) × Round A m | p.2.2.1 i=true} :=
    (measurableSet_observedSet i).preimage (by fun_prop)
  exact (measurable_const.ite hs measurable_const |>.const_mul
    ((1-Real.exp (-tilt))*C.triggerLower i)).sub
    (measurable_const.ite (hs.inter ho) measurable_const |>.const_mul tilt)

theorem integrable_exp_compensation {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (i : Fin m) (tilt scale : ℝ)
    (g : Ω → (Fin m → ℕ) × Round A m) (hg : Measurable g) :
    Integrable (fun ω => Real.exp (scale*C.compensation i tilt (g ω).1 (g ω).2)) ν := by
  apply (integrable_const (Real.exp (|scale| *(|(1-Real.exp (-tilt))*C.triggerLower i|+|tilt|)))).mono'
    (((C.measurable_compensation i tilt).comp hg).const_mul scale).exp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |scale*C.compensation i tilt (g ω).1 (g ω).2| := le_abs_self _
    _ = |scale| *|C.compensation i tilt (g ω).1 (g ω).2| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (C.compensation_abs_le _ _ _ _) (abs_nonneg _)

variable [Nonempty A]

theorem measurable_counters_piLE (n : ℕ) :
    Measurable[Filtration.piLE n] (fun Y : ℕ → Round A m => C.counters (fun t => (Y t).1) n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hf := (C.measurable_counters n).comp (measurable_prefixActions (A:=A) (m:=m) n)
  have hr : Measurable[MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
      (Preorder.frestrictLe (π:=fun _ : ℕ => Round A m) n) := Measurable.of_comap_le le_rfl
  convert hf.comp hr using 1
  funext Y
  apply C.counters_causal
  intro t ht
  simp [prefixActions, show t≤n by omega]

theorem compensation_adapted (i : Fin m) (tilt : ℝ) :
    StronglyAdapted Filtration.piLE (fun n (Y : ℕ → Round A m) =>
      C.compensation i tilt (C.counters (fun t => (Y t).1) n) (Y n)) := by
  intro n
  exact ((C.measurable_compensation i tilt).comp
    ((C.measurable_counters_piLE n).prodMk (measurable_round_piLE n))).stronglyMeasurable

variable [sA : StandardBorelSpace A]
variable (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
variable [IsMarkovKernel oracle] [IsMarkovKernel environment]
variable (i : Fin m) (htrigger : ∀a, i∈C.triggers a →
  C.triggerLower i≤(environment a (observedSet i)).toReal)
include htrigger sA

theorem charged_successor_condMGF (n : ℕ) (tilt : ℝ) (htilt : 0≤tilt) :
    Concentration.HasCondMGFUpperBoundAt
      (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
      (Preorder.measurable_frestrictLe n).comap_le
      (fun Y => C.compensation i tilt (C.counters (fun t => (Y t).1) (n+1)) (Y (n+1)))
      1 0 (cucbTrajectory oracle environment) := by
  apply Concentration.hasCondMGFUpperBoundAt_of_condExp_le
  · intro scale
    exact C.integrable_exp_compensation (cucbTrajectory oracle environment) i tilt scale
      (fun Y : ℕ → Round A m => (C.counters (fun t => (Y t).1) (n+1),Y (n+1)))
      (((C.measurable_counters (n+1)).comp
        (show Measurable (fun Y : ℕ → Round A m => fun t => (Y t).1) by fun_prop)).prodMk
          (measurable_pi_apply (n+1)))
  · simpa only [one_mul, Real.exp_zero, exp_compensation] using
      C.cucb_condExp_chargedTriggerFactor oracle environment i htrigger n tilt htilt

omit sA [Nonempty A] in
theorem charged_initial_MGF (tilt : ℝ) (htilt : 0≤tilt) :
    Concentration.HasMGFUpperBoundAt
      (fun Y => C.compensation i tilt (C.counters (fun t => (Y t).1) 0) (Y 0))
      1 0 (cucbTrajectory oracle environment) := by
  constructor
  · intro scale
    exact C.integrable_exp_compensation (cucbTrajectory oracle environment) i tilt scale
      (fun Y : ℕ → Round A m => ((fun _ => 0),Y 0))
      (measurable_const.prodMk (measurable_pi_apply 0))
  · simpa only [mgf, one_mul, Real.exp_zero, exp_compensation] using
      C.cucb_initial_chargedTriggerFactor oracle environment i htrigger tilt htilt

theorem charged_count_tail (n : ℕ) (tilt k budget : ℝ) (htilt : 0≤tilt)
    (hp : 0≤C.triggerLower i) :
    (cucbTrajectory oracle environment) {Y |
      k≤(C.counters (fun t => (Y t).1) n i : ℝ) ∧
      (C.chargedObservations Y n i : ℝ)≤budget} ≤
      ENNReal.ofReal (Real.exp (-((1-Real.exp (-tilt))*C.triggerLower i)*k+tilt*budget)) := by
  have hc : 0≤1-Real.exp (-tilt) := by
    have he := Real.exp_le_exp.mpr (show -tilt≤0 by linarith)
    rw [Real.exp_zero] at he
    linarith
  have h := Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
    (ℱ:=Filtration.piLE)
    (fun t Y => C.chargeValue i (C.counters (fun s => (Y s).1) t) (Y t))
    (fun t Y => C.successValue i (C.counters (fun s => (Y s).1) t) (Y t)) n
    ((1-Real.exp (-tilt))*C.triggerLower i) tilt k budget
    (C.compensation_adapted i tilt)
    (C.charged_initial_MGF oracle environment i htrigger tilt htilt)
    (fun t _ => by
      simpa only [Filtration.piLE_eq_comap_frestrictLe, compensation] using
        C.charged_successor_condMGF oracle environment i htrigger t tilt htilt)
    (mul_nonneg hc hp) htilt
  simpa only [sum_chargeValue, sum_successValue] using h

theorem observation_below_charged_half (n : ℕ) (k : ℝ) (hk : 0≤k)
    (hp : 0≤C.triggerLower i) :
    (cucbTrajectory oracle environment) {Y |
      k≤(C.counters (fun t => (Y t).1) n i : ℝ) ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤k*C.triggerLower i/2} ≤
      ENNReal.ofReal (Real.exp (-k*C.triggerLower i/8)) := by
  have hs : {Y : ℕ → Round A m |
      k≤(C.counters (fun t => (Y t).1) n i : ℝ) ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤k*C.triggerLower i/2} ⊆
      {Y | k≤(C.counters (fun t => (Y t).1) n i : ℝ) ∧
        (C.chargedObservations Y n i : ℝ)≤k*C.triggerLower i/2} := by
    intro Y hY
    have hh : (C.chargedObservations Y n i : ℝ)≤(observationCount (fun t => (Y t).2) n i : ℝ) := by
      exact_mod_cast C.chargedObservations_le_observationCount Y n i
    exact ⟨hY.1, hh.trans hY.2⟩
  have he : Real.exp (-Real.log 2)=(1/2:ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  calc
    _ ≤ (cucbTrajectory oracle environment) {Y |
      k≤(C.counters (fun t => (Y t).1) n i : ℝ) ∧
      (C.chargedObservations Y n i : ℝ)≤k*C.triggerLower i/2} := measure_mono hs
    _ ≤ ENNReal.ofReal (Real.exp (-((1-Real.exp (-Real.log 2))*C.triggerLower i)*k+
        Real.log 2*(k*C.triggerLower i/2))) :=
      C.charged_count_tail oracle environment i htrigger n (Real.log 2) k
        (k*C.triggerLower i/2) (Real.log_nonneg (by norm_num)) hp
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [he]
      have hl : Real.log 2≤(3/4:ℝ) := by linarith [Real.log_two_lt_d9]
      have hmul := mul_le_mul_of_nonneg_right hl (mul_nonneg hk hp)
      nlinarith

end ChargeData
end BanditRLProof.CUCB
