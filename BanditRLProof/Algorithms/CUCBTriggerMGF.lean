import BanditRLProof.Algorithms.CUCBObservationMGF

/-! Primitive Bernoulli exponential bound for actual triggered observations.
No stopping-time or adaptive-count tail is assumed here. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

noncomputable def triggerFactor {m : ℕ} (i : Fin m) (p tilt : ℝ) (z : Feedback m) : ℝ :=
  Real.exp (-tilt*(if z.1 i then 1 else 0)+(1-Real.exp (-tilt))*p)

theorem measurable_triggerFactor {m : ℕ} (i : Fin m) (p tilt : ℝ) :
    Measurable (triggerFactor i p tilt) := by
  unfold triggerFactor
  exact ((measurable_const.ite (measurableSet_observedSet i) measurable_const).const_mul
    (-tilt) |>.add_const ((1-Real.exp (-tilt))*p)).exp

theorem triggerFactor_nonneg {m : ℕ} (i : Fin m) (p tilt : ℝ) (z : Feedback m) :
    0≤triggerFactor i p tilt z := (Real.exp_pos _).le

theorem triggerFactor_le {m : ℕ} (i : Fin m) (p tilt : ℝ) (z : Feedback m) :
    triggerFactor i p tilt z≤Real.exp (|tilt|+|(1-Real.exp (-tilt))*p|) := by
  unfold triggerFactor
  apply Real.exp_le_exp.mpr
  cases z.1 i <;> simp only [Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, zero_add]
  · linarith [abs_nonneg tilt, le_abs_self ((1-Real.exp (-tilt))*p)]
  · linarith [neg_le_abs tilt, le_abs_self ((1-Real.exp (-tilt))*p)]

theorem triggerFactor_piecewise {m : ℕ} (i : Fin m) (p tilt : ℝ) [DecidablePred (· ∈ observedSet i)] :
    triggerFactor i p tilt = (observedSet i).piecewise
      (fun _ => Real.exp (-tilt+(1-Real.exp (-tilt))*p))
      (fun _ => Real.exp ((1-Real.exp (-tilt))*p)) := by
  classical
  funext z
  cases h : z.1 i <;> simp [triggerFactor, observedSet, Set.piecewise, h]

theorem integrable_triggerFactor {m : ℕ} (ν : Measure (Feedback m)) [IsProbabilityMeasure ν]
    (i : Fin m) (p tilt : ℝ) : Integrable (triggerFactor i p tilt) ν := by
  classical
  rw [triggerFactor_piecewise, ← Set.indicator_add_compl_eq_piecewise]
  exact ((integrable_const _).integrableOn.integrable_indicator (measurableSet_observedSet i)).add
    ((integrable_const _).integrableOn.integrable_indicator (measurableSet_observedSet i).compl)

theorem integral_triggerFactor {m : ℕ} (ν : Measure (Feedback m)) [IsProbabilityMeasure ν]
    (i : Fin m) (p tilt : ℝ) :
    (∫z, triggerFactor i p tilt z ∂ν) =
      (1-(ν (observedSet i)).toReal*(1-Real.exp (-tilt)))*
        Real.exp ((1-Real.exp (-tilt))*p) := by
  classical
  rw [triggerFactor_piecewise, integral_piecewise (measurableSet_observedSet i)
    (integrable_const _) (integrable_const _)]
  have ht := measureReal_add_measureReal_compl (μ:=ν) (measurableSet_observedSet i)
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at ht
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, Real.exp_add]
  have hc : (ν ((observedSet i)ᶜ)).toReal=1-(ν (observedSet i)).toReal := by linarith
  rw [hc]
  ring

theorem integral_triggerFactor_le_one {m : ℕ} (ν : Measure (Feedback m))
    [IsProbabilityMeasure ν] (i : Fin m) (p tilt : ℝ)
    (hp : p≤(ν (observedSet i)).toReal) (htilt : 0≤tilt) :
    (∫z, triggerFactor i p tilt z ∂ν)≤1 := by
  rw [integral_triggerFactor]
  have hc : 0≤1-Real.exp (-tilt) := by
    have h := Real.exp_le_exp.mpr (show -tilt≤0 by linarith)
    rw [Real.exp_zero] at h
    linarith
  have he := Real.add_one_le_exp (-((1-Real.exp (-tilt))*p))
  calc
    _ ≤ (1-p*(1-Real.exp (-tilt)))*Real.exp ((1-Real.exp (-tilt))*p) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
    _ ≤ Real.exp (-((1-Real.exp (-tilt))*p))*Real.exp ((1-Real.exp (-tilt))*p) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end BanditRLProof.CUCB
