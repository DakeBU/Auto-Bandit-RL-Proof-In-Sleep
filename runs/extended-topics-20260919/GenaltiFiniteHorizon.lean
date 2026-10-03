import BanditRLProof.Algorithms.HeavyTailRegret
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace BanditRLProof.HeavyTail.GenaltiAudit

theorem mean_abs_le_raw_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ε u : ℝ) (hε : 0 ≤ ε) (hu : 0 < u)
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) μ)
    (hbound : (∫ x, |x|^(1+ε) ∂μ) ≤ u) :
    |∫ x, x ∂μ| ≤ u^(1/(1+ε)) := by
  have hi := integrable_id_of_raw_moment μ ε hε hm
  have hj := (convexOn_rpow (show 1 ≤ 1+ε by linarith)).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ 1+ε)).continuousOn
    isClosed_Ici (ae_of_all μ fun x : ℝ => abs_nonneg x) hi.abs hm
  have hnon : 0 ≤ ∫ x, |x| ∂μ := integral_nonneg fun x => abs_nonneg x
  have hscale : (u^(1/(1+ε)))^(1+ε) = u := by
    rw [one_div, Real.rpow_inv_rpow hu.le (by linarith)]
  have hroot : (∫ x, |x| ∂μ) ≤ u^(1/(1+ε)) := by
    apply (Real.rpow_le_rpow_iff hnon (Real.rpow_nonneg hu.le _) (by linarith : 0 < 1+ε)).mp
    rw [hscale]
    exact hj.trans hbound
  exact (abs_integral_le_integral_abs).trans hroot

theorem trace_regret_bounds {K : ℕ} (hK : 0 < K) (m : Fin K → ℝ)
    (s : ℝ) (hs : 0 ≤ s) (hm : ∀ i, |m i| ≤ s)
    (action : ActionTrace (Fin K)) (T : ℕ) :
    0 ≤ realMeanRegret m action T ∧ realMeanRegret m action T ≤ 2*T*s := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have hb : BddAbove (Set.range m) := ⟨s, by rintro _ ⟨i,rfl⟩; exact (abs_le.mp (hm i)).2⟩
  have hsup : (⨆ i, m i) ≤ s := ciSup_le fun i => (abs_le.mp (hm i)).2
  have hg : ∀ i, 0 ≤ realMeanGap m i ∧ realMeanGap m i ≤ 2*s := by
    intro i
    dsimp [realMeanGap]
    constructor
    · exact sub_nonneg.mpr (le_ciSup hb i)
    · have hl := (abs_le.mp (hm i)).1
      linarith
  rw [realMeanRegret_eq_finset_sum_gap]
  constructor
  · exact Finset.sum_nonneg fun t _ => (hg (action t)).1
  · calc
      ∑ t ∈ Finset.range T, realMeanGap m (action t) ≤ ∑ _t ∈ Finset.range T, 2*s :=
        Finset.sum_le_sum fun t _ => (hg (action t)).2
      _ = 2*T*s := by simp; ring

theorem expected_normalized_regret_le {K : ℕ} (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (ε u : ℝ) (hε : 0 ≤ ε) (hu : 0 < u)
    (hm : ∀ i, Integrable (fun x : ℝ => |x|^(1+ε)) (ν i))
    (hb : ∀ i, (∫ x, |x|^(1+ε) ∂ν i) ≤ u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (action : Ω → ActionTrace (Fin K)) (T : ℕ)
    (ha : ∀ t, Measurable (fun ω => action ω t)) :
    (∫ ω, realMeanRegret (realKernelMean ν) (action ω) T ∂P) /
      u^(1/(1+ε)) ≤ 2*T := by
  let s := u^(1/(1+ε))
  have hs : 0 < s := Real.rpow_pos_of_pos hu _
  have hmeans : ∀ i, |realKernelMean ν i| ≤ s := fun i =>
    mean_abs_le_raw_scale (ν i) ε u hε hu (hm i) (hb i)
  have hpath := fun ω => trace_regret_bounds hK (realKernelMean ν) s hs.le hmeans (action ω) T
  have hmeas : Measurable (fun ω => realMeanRegret (realKernelMean ν) (action ω) T) := by
    simp_rw [realMeanRegret_eq_finset_sum_gap]
    exact Finset.measurable_sum _ fun t _ =>
      (measurable_of_finite (realMeanGap (realKernelMean ν))).comp (ha t)
  have hi : Integrable (fun ω => realMeanRegret (realKernelMean ν) (action ω) T) P := by
    apply (integrable_const (2*(T:ℝ)*s)).mono' hmeas.aestronglyMeasurable
    exact ae_of_all P fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpath ω).1]
      exact (hpath ω).2
  apply (div_le_iff₀ hs).mpr
  calc
    (∫ ω, realMeanRegret (realKernelMean ν) (action ω) T ∂P) ≤ ∫ _ω, 2*(T:ℝ)*s ∂P :=
      integral_mono hi (integrable_const _) fun ω => (hpath ω).2
    _ = 2*T*s := by simp

#print axioms expected_normalized_regret_le
end BanditRLProof.HeavyTail.GenaltiAudit
