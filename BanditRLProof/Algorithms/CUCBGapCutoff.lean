import BanditRLProof.Algorithms.CUCBRefinedRegret
import BanditRLProof.FiniteGapCutoff

/-! Actual gap cutoff bound used by the distribution-independent CUCB proof.
The baseline is paid once per round, not once per arm threshold crossing. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

theorem card_underChargeTimes_le (H : ℕ) (actions : ℕ → A) (i : Fin m) :
    (S.underChargeTimes H actions i).card≤S.chargeData.counters actions H i := by
  classical
  calc
    _ ≤ ((Finset.range H).filter (fun t =>
        S.chargeData.choose (S.chargeData.counters actions t) (actions t)=some i)).card := by
      apply Finset.card_le_card
      intro t ht
      have h := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨h.1,h.2.1⟩
    _ = _ := by rw [ChargeData.counters_eq_sum]; simp

theorem sum_card_underChargeTimes_le (H : ℕ) (actions : ℕ → A) :
    (∑i:Fin m, ((S.underChargeTimes H actions i).card:ℝ))≤H := by
  have hc := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => S.card_underChargeTimes_le H actions i)
  have hN : (∑i:Fin m, S.chargeData.counters actions H i)≤H := by
    rw [ChargeData.counters_sum]
    calc
      _ ≤ ∑_t∈Finset.range H, (1:ℕ) := Finset.sum_le_sum (fun t _ => by split_ifs <;> omega)
      _ = H := by simp
  exact_mod_cast hc.trans hN

theorem underChargeWeight_le_cutoff (H : ℕ) (hH : 1≤H) (actions : ℕ → A) (i : Fin m)
    (a : ℝ) (ha : a∈S.gapDomain) : S.underChargeWeight H actions i≤
      a*((S.underChargeTimes H actions i).card:ℝ)+
      (∫x in a..maxPositiveGap S.score M.trueInput S.alpha, S.gapThreshold H (M.minTrigger i) x)+
      (maxPositiveGap S.score M.trueInput S.alpha-a) := by
  have hD : maxPositiveGap S.score M.trueInput S.alpha∈S.gapDomain := ⟨ha.1.trans_le ha.2,le_rfl⟩
  apply FiniteGapLayerCake.sum_le_cutoff_integral _ _ _ _ ha.2
  · intro t _
    exact gap_le_maxPositiveGap S.score M.trueInput S.alpha (actions t)
  · exact S.gapThreshold_intervalIntegrable H hH _ (M.minTrigger_pos i) ha hD
  · intro x hx
    exact S.card_underChargeGapTail_le H hH actions i x ⟨ha.1.trans_le hx.1,hx.2⟩

theorem sum_underSampledGap_le_cutoff (H : ℕ) (hH : 1≤H) (actions : ℕ → A)
    (a : ℝ) (ha : a∈S.gapDomain) :
    (∑t∈Finset.range H, S.underSampledGap H (S.chargeData.counters actions t) (actions t))≤
      (H:ℝ)*a+(∑i:Fin m, ∫x in a..maxPositiveGap S.score M.trueInput S.alpha,
        S.gapThreshold H (M.minTrigger i) x)+(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  rw [S.sum_underSampledGap_eq_weights]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => S.underChargeWeight_le_cutoff H hH actions i a ha)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← Finset.mul_sum] at h
  have hc := mul_le_mul_of_nonneg_left (S.sum_card_underChargeTimes_le H actions) ha.1.le
  have hm : 0≤(m:ℝ)*a := mul_nonneg (Nat.cast_nonneg m) ha.1.le
  nlinarith

variable [MeasurableSingletonClass A] [StandardBorelSpace A]

theorem approximationRegret_le_gap_cutoff (H : ℕ) (hH : 1≤H) (a : ℝ) (ha : a∈S.gapDomain) :
    S.approximationRegret H≤(H:ℝ)*a+
      (∑i:Fin m, ∫x in a..maxPositiveGap S.score M.trueInput S.alpha, S.gapThreshold H (M.minTrigger i) x)+
      (1+(2+(if M.globalMinTrigger<1 then 1 else 0))*Real.pi^2/6)*
        (m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hi := integral_mono
    (integrable_finset_sum (Finset.range H) (fun n _ => S.integrable_actual_underSampledGap H n))
    (integrable_const _) (fun Y => S.sum_underSampledGap_le_cutoff H hH (fun t => (Y t).1) a ha)
  rw [integral_finset_sum _ (fun n _ => S.integrable_actual_underSampledGap H n)] at hi
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  have h := S.approximationRegret_le_underSampled_add_source_tail H
  calc
    _ ≤ _ := h.trans (add_le_add hi le_rfl)
    _ = _ := by ring

theorem approximationRegret_le_large_cutoff (H : ℕ) (a : ℝ)
    (ha : maxPositiveGap S.score M.trueInput S.alpha≤a) :
    S.approximationRegret H≤(H:ℝ)*a+
      (2+(if M.globalMinTrigger<1 then 1 else 0))*(m:ℝ)*
        maxPositiveGap S.score M.trueInput S.alpha*Real.pi^2/6 := by
  have hround (n : ℕ) :
      (∫Y : ℕ → Round A m, S.underSampledGap H
        (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1 ∂cucbTrajectory S.oracle M.environment)≤a := by
    have h := integral_mono (S.integrable_actual_underSampledGap H n) (integrable_const a)
      (fun Y => (S.underSampledGap_mem H _ _).2.trans ha)
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h
  have hs := Finset.sum_le_sum (s:=Finset.range H) (fun n _ => hround n)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  exact (S.approximationRegret_le_underSampled_add_source_tail H).trans (add_le_add hs le_rfl)

end BanditRLProof.CUCB.SourceModel
