import BanditRLProof.Algorithms.HeavyTailRegret
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.EReal.Basic

/-!
Finite raw-moment regret cap and extended-real supremum obstruction.
Source: Genalti et al., COLT2024, Theorem2 Eq5. This enlarged trace-law class
supplies an upper obstruction, not a fixed-algorithm lower bound or an
asymptotic impossibility theorem. See the paired reader page and source deltas.
-/

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



/-- Actual values, with moment laws and trace laws as witnesses, not a bound premise. -/
def normalizedValues (K : ℕ) (ε : ℝ) (T : ℕ) : Set EReal :=
  {r | ∃ (u : ℝ), 0 < u ∧ ∃ (ν : Kernel (Fin K) ℝ),
    IsMarkovKernel ν ∧
    (∀ i, Integrable (fun x : ℝ => |x|^(1+ε)) (ν i)) ∧
    (∀ i, (∫ x, |x|^(1+ε) ∂ν i) ≤ u) ∧
    ∃ (P : Measure (ActionTrace (Fin K))), IsProbabilityMeasure P ∧
      r = (((∫ a, realMeanRegret (realKernelMean ν) a T ∂P) /
        u^(1/(1+ε)) : ℝ) : EReal)}

theorem normalizedValues_le {K : ℕ} (hK : 0 < K) (ε : ℝ) (hε : 0 ≤ ε)
    (T : ℕ) {r : EReal} (hr : r ∈ normalizedValues K ε T) :
    r ≤ ((2*(T:ℝ) : ℝ) : EReal) := by
  rcases hr with ⟨u,hu,ν,hν,hm,hb,P,hP,rfl⟩
  letI := hν
  letI := hP
  apply EReal.coe_le_coe_iff.mpr
  exact expected_normalized_regret_le hK ν ε u hε hu hm hb P
    (fun a => a) T (fun t => measurable_pi_apply t)

theorem normalized_sSup_le {K : ℕ} (hK : 0 < K) (ε : ℝ) (hε : 0 ≤ ε) (T : ℕ) :
    sSup (normalizedValues K ε T) ≤ ((2*(T:ℝ) : ℝ) : EReal) :=
  sSup_le fun _ hr => normalizedValues_le hK ε hε T hr

theorem normalized_sSup_ne_top {K : ℕ} (hK : 0 < K) (ε : ℝ) (hε : 0 ≤ ε) (T : ℕ) :
    sSup (normalizedValues K ε T) ≠ ⊤ :=
  ne_of_lt ((normalized_sSup_le hK ε hε T).trans_lt (EReal.coe_lt_top _))

/-- Arbitrary measurable action processes enter the set via their actual image law. -/
theorem process_value_mem {K : ℕ}
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (ε u : ℝ) (hu : 0 < u)
    (hm : ∀ i, Integrable (fun x : ℝ => |x|^(1+ε)) (ν i))
    (hb : ∀ i, (∫ x, |x|^(1+ε) ∂ν i) ≤ u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (action : Ω → ActionTrace (Fin K)) (ha : ∀ t, Measurable (fun ω => action ω t))
    (T : ℕ) :
    (((∫ ω, realMeanRegret (realKernelMean ν) (action ω) T ∂P) /
      u^(1/(1+ε)) : ℝ) : EReal) ∈ normalizedValues K ε T := by
  have haction : Measurable action := measurable_pi_lambda _ ha
  have hmeas : Measurable (fun a : ActionTrace (Fin K) => realMeanRegret (realKernelMean ν) a T) := by
    simp_rw [realMeanRegret_eq_finset_sum_gap]
    exact Finset.measurable_sum _ fun t _ =>
      (measurable_of_finite (realMeanGap (realKernelMean ν))).comp (measurable_pi_apply t)
  refine ⟨u,hu,ν,inferInstance,hm,hb,P.map action,
    Measure.isProbabilityMeasure_map haction.aemeasurable,?_⟩
  rw [integral_map haction.aemeasurable hmeas.aestronglyMeasurable]

noncomputable def extremeKernel : Kernel (Fin 2) ℝ :=
  Kernel.ofFunOfCountable (fun i => Measure.dirac (if i=0 then (1:ℝ) else -1))

@[simp] theorem extreme_apply (i : Fin 2) :
    extremeKernel i = Measure.dirac (if i=0 then (1:ℝ) else -1) := rfl

instance extreme_markov : IsMarkovKernel extremeKernel := by
  constructor
  intro i
  rw [extreme_apply]
  infer_instance

theorem extreme_moment (i : Fin 2) :
    Integrable (fun x : ℝ => |x|^(1+(1:ℝ))) (extremeKernel i) ∧
    (∫ x, |x|^(1+(1:ℝ)) ∂extremeKernel i) ≤ 1 := by
  rw [extreme_apply]
  constructor
  · exact integrable_dirac (by finiteness)
  · rw [integral_dirac]
    split <;> norm_num

@[simp] theorem extreme_mean (i : Fin 2) :
    realKernelMean extremeKernel i = if i=0 then 1 else -1 := by
  simp [realKernelMean]

theorem extreme_best : (⨆ i : Fin 2, realKernelMean extremeKernel i) = 1 := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    rw [extreme_mean]
    split <;> norm_num
  · have h := le_ciSup (Finite.bddAbove_range (realKernelMean extremeKernel)) (0:Fin 2)
    have hz : realKernelMean extremeKernel (0:Fin 2) = 1 := by simp
    exact hz.symm.le.trans h

theorem extreme_trace_regret (T : ℕ) :
    realMeanRegret (realKernelMean extremeKernel) (fun _ => 1) T = 2*T := by
  rw [realMeanRegret, extreme_best]
  simp only [extreme_mean, show (1:Fin 2) ≠ 0 by decide, if_false, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem cap_mem (T : ℕ) : ((2*(T:ℝ) : ℝ) : EReal) ∈ normalizedValues 2 1 T := by
  refine ⟨1,by norm_num,extremeKernel,inferInstance,
    fun i => (extreme_moment i).1,fun i => (extreme_moment i).2,
    Measure.dirac (fun _ : ℕ => (1:Fin 2)),inferInstance,?_⟩
  simp [integral_dirac,extreme_trace_regret]

theorem normalized_sSup_two_eq (T : ℕ) :
    sSup (normalizedValues 2 1 T) = ((2*(T:ℝ) : ℝ) : EReal) := by
  exact le_antisymm (normalized_sSup_le (by decide) 1 (by norm_num) T) (le_sSup (cap_mem T))

end BanditRLProof.HeavyTail.GenaltiAudit
