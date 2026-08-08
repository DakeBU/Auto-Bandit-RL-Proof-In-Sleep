import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# L2 control of an indicator-restricted integral

This is the nonnegative `2,2` Holder specialization used to turn an event
probability bound and an exact second moment into an expected overflow bound.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace BanditRLProof

universe u

/-- A nonnegative `L2` function restricted to a measurable event is controlled
by its exact second moment and the square root of the event's real mass. -/
theorem integral_indicator_le_sqrt_secondMoment_mul_sqrt_real_measure
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega -> Real)
    (hf_nonneg : forall omega, 0 <= f omega)
    (hf : MemLp f 2 mu)
    (event : Set Omega) (hevent : MeasurableSet event) :
    integral mu (event.indicator f) <=
      Real.sqrt (integral mu (fun omega => f omega ^ 2)) *
        Real.sqrt (mu.real event) := by
  let indicatorOne : Omega -> Real := event.indicator (fun _ => 1)
  have hpq : (2 : Real).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hindicatorOne_nonneg : forall omega, 0 <= indicatorOne omega := by
    intro omega
    by_cases homega : omega ∈ event <;> simp [indicatorOne, homega]
  have hindicatorOne : MemLp indicatorOne 2 mu := by
    exact memLp_indicator_const 2 hevent 1
      (Or.inr (measure_lt_top mu event).ne)
  have hf_realTwo : MemLp f (ENNReal.ofReal (2 : Real)) mu := by
    norm_num
    exact hf
  have hindicatorOne_realTwo :
      MemLp indicatorOne (ENNReal.ofReal (2 : Real)) mu := by
    norm_num
    exact hindicatorOne
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Filter.Eventually.of_forall hf_nonneg)
      (Filter.Eventually.of_forall hindicatorOne_nonneg)
      hf_realTwo hindicatorOne_realTwo
  have hmul :
      (fun omega => f omega * indicatorOne omega) = event.indicator f := by
    funext omega
    by_cases homega : omega ∈ event <;> simp [indicatorOne, homega]
  have hpow :
      (fun omega => indicatorOne omega ^ (2 : Real)) =
        event.indicator (fun _ => (1 : Real)) := by
    funext omega
    by_cases homega : omega ∈ event <;> simp [indicatorOne, homega]
  have hintegralIndicatorOne :
      integral mu (event.indicator (fun _ => (1 : Real))) = mu.real event := by
    simpa using (integral_indicator_one (μ := mu) hevent)
  rw [hmul, hpow, hintegralIndicatorOne] at hholder
  simp_rw [Real.rpow_two] at hholder
  simpa only [Real.sqrt_eq_rpow] using hholder

end BanditRLProof
