import BanditRLProof.Algorithms.CUCBActualReward
import BanditRLProof.Algorithms.CUCBSufficientSampling

/-! Actual charged-gap decomposition preserving the signed oracle-failure credit. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

noncomputable def underSampledGap (H : ℕ) (N : Fin m → ℕ) (a : A) : ℝ := by
  classical
  exact if ∃i, S.chargeData.choose N a=some i ∧
    (N i:ℝ)≤samplingThreshold H (S.inverseGap a) (M.minTrigger i)
    then max 0 (S.gap a) else 0

noncomputable def sufficientIndicator (H n : ℕ) (Y : ℕ → Round A m) : ℝ := by
  classical
  exact if Y∈S.SufficientSuccessfulCharge H n then 1 else 0

theorem maxPositiveGap_nonneg : 0≤maxPositiveGap S.score M.trueInput S.alpha := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact (le_max_left (0:ℝ) (S.gap a)).trans
    (Finset.le_sup' (fun a => max 0 (sourceGap S.score M.trueInput S.alpha a)) (Finset.mem_univ a))

theorem underSampledGap_mem (H : ℕ) (N : Fin m → ℕ) (a : A) :
    S.underSampledGap H N a∈Set.Icc 0 (maxPositiveGap S.score M.trueInput S.alpha) := by
  unfold underSampledGap
  split_ifs
  · exact ⟨le_max_left _ _, Finset.le_sup' (fun b => max 0 (sourceGap S.score M.trueInput S.alpha b)) (Finset.mem_univ a)⟩
  · exact ⟨le_rfl, S.maxPositiveGap_nonneg⟩

theorem sufficientIndicator_mem (H n : ℕ) (Y : ℕ → Round A m) :
    S.sufficientIndicator H n Y∈Set.Icc (0:ℝ) 1 := by
  unfold sufficientIndicator
  split_ifs <;> norm_num

theorem gap_decomposition (H n : ℕ) (Y : ℕ → Round A m) :
    S.gap (Y n).1≤S.underSampledGap H (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1 +
      maxPositiveGap S.score M.trueInput S.alpha*S.sufficientIndicator H n Y +
      S.alpha*scoreOptimum S.score M.trueInput*
        (1-S.successIndicator (oracleInput (fun t => (Y t).2) n) (Y n)) := by
  classical
  let N := S.chargeData.counters (fun t => (Y t).1) n
  let a := (Y n).1
  have hu := (S.underSampledGap_mem H N a).1
  have hs := mul_nonneg S.maxPositiveGap_nonneg (S.sufficientIndicator_mem H n Y).1
  have ho : 0≤S.alpha*scoreOptimum S.score M.trueInput :=
    mul_nonneg S.alpha_mem.1.le ((S.score_nonneg M.trueInput a).trans (score_le_optimum _ _ a))
  have hf := mul_nonneg ho (sub_nonneg.mpr (S.successIndicator_mem (oracleInput (fun t => (Y t).2) n) (Y n)).2)
  change S.gap a≤S.underSampledGap H N a+_+_
  by_cases hgap : 0<S.gap a
  · have hb : S.chargeData.bad a=true := by simp [chargeData, FeedbackModel.chargeData, bad, hgap]
    cases hc : S.chargeData.choose N a with
    | none => simp [ChargeData.choose, hb] at hc
    | some i =>
      by_cases ht : (N i:ℝ)≤samplingThreshold H (S.inverseGap a) (M.minTrigger i)
      · have he : S.underSampledGap H N a=S.gap a := by
          rw [underSampledGap, if_pos ⟨i,hc,ht⟩, max_eq_right hgap.le]
        rw [he]
        linarith
      · by_cases hok : (oracleInput (fun t => (Y t).2) n,a)∈S.oracleSuccess
        · have hmem : Y∈S.SufficientSuccessfulCharge H n := ⟨i,hc,not_le.mp ht,hok⟩
          have he : S.sufficientIndicator H n Y=1 := by simp [sufficientIndicator,hmem]
          rw [he, mul_one]
          have hg := gap_le_maxPositiveGap S.score M.trueInput S.alpha a
          change S.gap a≤_ at hg
          linarith
        · have he : S.successIndicator (oracleInput (fun t => (Y t).2) n) (Y n)=0 := by
            simp [successIndicator, hok, a]
          rw [he, sub_zero, mul_one]
          have hg : S.gap a≤S.alpha*scoreOptimum S.score M.trueInput := by
            unfold gap sourceGap
            linarith [S.score_nonneg M.trueInput a]
          linarith
  · exact (not_lt.mp hgap).trans (by linarith)




variable [MeasurableSingletonClass A]

theorem measurable_actual_underSampledGap (H n : ℕ) : Measurable (fun Y : ℕ → Round A m =>
    S.underSampledGap H (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1) :=
  (measurable_of_countable (f:=fun p : (Fin m → ℕ) × A => S.underSampledGap H p.1 p.2)).comp
    (((S.chargeData.measurable_counters n).comp (by fun_prop)).prodMk (by fun_prop))

theorem measurableSet_sufficientSuccessfulCharge (H n : ℕ) :
    MeasurableSet (S.SufficientSuccessfulCharge H n) := by
  classical
  let B : Set ((Fin m → ℕ) × A) := {p | ∃i, S.chargeData.choose p.1 p.2=some i ∧
    samplingThreshold H (S.inverseGap p.2) (M.minTrigger i)<(p.1 i:ℝ)}
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have hstate : Measurable (fun Y : ℕ → Round A m =>
      (S.chargeData.counters (fun t => (Y t).1) n,(Y n).1)) :=
    ((S.chargeData.measurable_counters n).comp (by fun_prop)).prodMk (by fun_prop)
  convert (hB.preimage hstate).inter (S.measurableSet_path_oracleSuccess n) using 1
  ext Y
  simp only [SufficientSuccessfulCharge, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, B, oracleSuccess]
  aesop

theorem integrable_actual_underSampledGap (H n : ℕ) : Integrable (fun Y : ℕ → Round A m =>
    S.underSampledGap H (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1)
      (cucbTrajectory S.oracle M.environment) := by
  apply (integrable_const (maxPositiveGap S.score M.trueInput S.alpha)).mono'
    (S.measurable_actual_underSampledGap H n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro Y
  rw [Real.norm_eq_abs, abs_of_nonneg (S.underSampledGap_mem H _ _).1]
  exact (S.underSampledGap_mem H _ _).2

theorem integrable_sufficientIndicator (H n : ℕ) :
    Integrable (S.sufficientIndicator H n) (cucbTrajectory S.oracle M.environment) := by
  have hm : Measurable (S.sufficientIndicator H n) :=
    measurable_const.ite (S.measurableSet_sufficientSuccessfulCharge H n) measurable_const
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro Y
  rw [Real.norm_eq_abs, abs_of_nonneg (S.sufficientIndicator_mem H n Y).1]
  exact (S.sufficientIndicator_mem H n Y).2

variable [StandardBorelSpace A]

theorem expected_gap_decomposition (H n : ℕ) :
    (∫Y : ℕ → Round A m, S.gap (Y n).1 ∂cucbTrajectory S.oracle M.environment) ≤
      (∫Y : ℕ → Round A m, S.underSampledGap H
        (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1 ∂cucbTrajectory S.oracle M.environment) +
      maxPositiveGap S.score M.trueInput S.alpha*
        (∫Y, S.sufficientIndicator H n Y ∂cucbTrajectory S.oracle M.environment) +
      S.alpha*scoreOptimum S.score M.trueInput*(1-S.beta) := by
  let P := cucbTrajectory S.oracle M.environment
  let G := S.alpha*scoreOptimum S.score M.trueInput
  let D := maxPositiveGap S.score M.trueInput S.alpha
  have hsuccess : Integrable (fun Y : ℕ → Round A m =>
      S.successIndicator (oracleInput (fun t => (Y t).2) n) (Y n)) P :=
    S.integrable_successIndicator_comp P (fun Y => (oracleInput (fun t => (Y t).2) n,Y n))
      (((measurable_oracleInput n).comp (by fun_prop)).prodMk (by fun_prop))
  have hu := S.integrable_actual_underSampledGap H n
  have hs := (S.integrable_sufficientIndicator H n).const_mul D
  have hf := ((integrable_const (1:ℝ)).sub hsuccess).const_mul G
  have h := integral_mono (S.integrable_actual_gap n) ((hu.add hs).add hf)
    (S.gap_decomposition H n)
  simp only [Pi.add_apply, Pi.sub_apply] at h hf
  have he := integral_add (hu.add hs) hf
  simp only [Pi.add_apply] at he
  rw [he, integral_add hu hs, integral_const_mul,
    integral_const_mul, integral_sub (integrable_const (1:ℝ)) hsuccess] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have hG : 0≤G := by
    obtain ⟨a⟩ := ‹Nonempty A›
    exact mul_nonneg S.alpha_mem.1.le
      ((S.score_nonneg M.trueInput a).trans (score_le_optimum _ _ a))
  have hb := mul_le_mul_of_nonneg_left
    (sub_le_sub_left (S.expected_oracle_success n) 1) hG
  exact h.trans (add_le_add le_rfl hb)

/-- Exact cancellation against the negative credit in the original signed
approximation regret. The under-count term is still the actual random weight. -/
theorem approximationRegret_le_underSampled_add_sufficient (H : ℕ) :
    S.approximationRegret H ≤
      (∑n∈Finset.range H, ∫Y : ℕ → Round A m, S.underSampledGap H
        (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1 ∂cucbTrajectory S.oracle M.environment) +
      maxPositiveGap S.score M.trueInput S.alpha*
        ∑n∈Finset.range H, ∫Y, S.sufficientIndicator H n Y ∂cucbTrajectory S.oracle M.environment := by
  rw [S.approximationRegret_eq_gap_sum,
    integral_finset_sum _ (fun n _ => S.integrable_actual_gap n)]
  have h := Finset.sum_le_sum (s:=Finset.range H) (fun n _ => S.expected_gap_decomposition H n)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at h
  nlinarith

end BanditRLProof.CUCB.SourceModel
