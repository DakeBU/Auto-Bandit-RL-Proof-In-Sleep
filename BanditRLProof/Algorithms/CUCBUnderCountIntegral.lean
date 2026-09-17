import BanditRLProof.Algorithms.CUCBUnderCount
import BanditRLProof.FiniteGapLayerCake

/-! Refined integral bound for the actual under-sampled charge weights. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

noncomputable def underChargeWeight (H : ℕ) (actions : ℕ → A) (i : Fin m) : ℝ :=
  ∑t∈S.underChargeTimes H actions i, S.gap (actions t)

theorem underChargeWeight_le_refined (H : ℕ) (hH : 1≤H) (actions : ℕ → A) (i : Fin m)
    (hi : (S.badActions i).Nonempty) :
    S.underChargeWeight H actions i ≤
      S.minBadGap i hi*S.gapThreshold H (M.minTrigger i) (S.minBadGap i hi)+
      (∫x in S.minBadGap i hi..S.maxBadGap i hi, S.gapThreshold H (M.minTrigger i) x)+
      S.maxBadGap i hi := by
  have hb := S.badGap_bounds i hi
  apply FiniteGapLayerCake.sum_le_refined_integral _ _ _ _ hb.1.1.le hb.2.2
  · intro t ht
    have ha := S.underChargeTimes_mem_badActions H actions i ht
    exact ⟨Finset.inf'_le S.gap ha,Finset.le_sup' S.gap ha⟩
  · exact S.gapThreshold_intervalIntegrable H hH _ (M.minTrigger_pos i) hb.1 hb.2.1
  · intro x hx
    exact S.card_underChargeGapTail_le H hH actions i x
      ⟨lt_of_lt_of_le hb.1.1 hx.1,hx.2.trans hb.2.1.2⟩

noncomputable def armRefinedTerm (H : ℕ) (i : Fin m) : ℝ := by
  classical
  exact if hi : (S.badActions i).Nonempty then
    S.minBadGap i hi*S.gapThreshold H (M.minTrigger i) (S.minBadGap i hi)+
      (∫x in S.minBadGap i hi..S.maxBadGap i hi, S.gapThreshold H (M.minTrigger i) x)
    else 0

theorem underChargeWeight_le_armRefinedTerm (H : ℕ) (hH : 1≤H) (actions : ℕ → A)
    (i : Fin m) : S.underChargeWeight H actions i≤
      S.armRefinedTerm H i+maxPositiveGap S.score M.trueInput S.alpha := by
  classical
  by_cases hi : (S.badActions i).Nonempty
  · rw [armRefinedTerm, dif_pos hi]
    exact (S.underChargeWeight_le_refined H hH actions i hi).trans
      (add_le_add le_rfl (S.badGap_bounds i hi).2.1.2)
  · rw [armRefinedTerm, dif_neg hi, zero_add, underChargeWeight,
      S.underChargeTimes_empty_of_no_bad H actions i (Finset.not_nonempty_iff_eq_empty.mp hi),
      Finset.sum_empty]
    exact S.maxPositiveGap_nonneg

theorem underSampledGap_eq_sum_arms (H : ℕ) (N : Fin m → ℕ) (a : A) :
    S.underSampledGap H N a=∑i:Fin m, if S.chargeData.choose N a=some i ∧
      (N i:ℝ)≤samplingThreshold H (S.inverseGap a) (M.minTrigger i) then S.gap a else 0 := by
  classical
  by_cases h : ∃i, S.chargeData.choose N a=some i ∧
      (N i:ℝ)≤samplingThreshold H (S.inverseGap a) (M.minTrigger i)
  · obtain ⟨i,hi,hN⟩ := h
    have hgap : 0<S.gap a := by
      have hb := (S.chargeData.choose_mem N a i hi).1
      simpa [chargeData,FeedbackModel.chargeData,bad] using hb
    have he (j : Fin m) : (S.chargeData.choose N a=some j ∧
        (N j:ℝ)≤samplingThreshold H (S.inverseGap a) (M.minTrigger j)) ↔ j=i := by
      constructor
      · intro hj
        exact (Option.some.inj (hi.symm.trans hj.1)).symm
      · rintro rfl
        exact ⟨hi,hN⟩
    rw [underSampledGap, if_pos ⟨i,hi,hN⟩, max_eq_right hgap.le]
    simp [he]
  · rw [underSampledGap, if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (fun hi => h ⟨i,hi⟩)]

theorem sum_underSampledGap_eq_weights (H : ℕ) (actions : ℕ → A) :
    (∑t∈Finset.range H, S.underSampledGap H (S.chargeData.counters actions t) (actions t))=
      ∑i:Fin m, S.underChargeWeight H actions i := by
  classical
  simp_rw [S.underSampledGap_eq_sum_arms]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [underChargeWeight,underChargeTimes,Finset.sum_filter]

theorem sum_underSampledGap_le_refined (H : ℕ) (hH : 1≤H) (actions : ℕ → A) :
    (∑t∈Finset.range H, S.underSampledGap H (S.chargeData.counters actions t) (actions t))≤
      (∑i:Fin m, S.armRefinedTerm H i)+(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  rw [S.sum_underSampledGap_eq_weights]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    S.underChargeWeight_le_armRefinedTerm H hH actions i)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    using h

end BanditRLProof.CUCB.SourceModel
