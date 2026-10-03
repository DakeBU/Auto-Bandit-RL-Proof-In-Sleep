import BanditRLProof.Algorithms.CUCBUnderCountIntegral
import BanditRLProof.Algorithms.CUCBRegretTail

/-! The full refined integral approximation-regret endpoint, with the disclosed
normalized analysis-counter repair and the unchanged source CUCB learner. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [StandardBorelSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

omit [StandardBorelSpace A] in
theorem expected_underSampledGap_le_refined (H : ℕ) (hH : 1≤H) :
    (∑n∈Finset.range H, ∫Y : ℕ → Round A m, S.underSampledGap H
      (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1 ∂cucbTrajectory S.oracle M.environment) ≤
      (∑i:Fin m, S.armRefinedTerm H i)+(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hu := integrable_finset_sum (Finset.range H) (fun n _ => S.integrable_actual_underSampledGap H n)
  have h := integral_mono hu (integrable_const
    ((∑i:Fin m, S.armRefinedTerm H i)+(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha))
    (fun Y => S.sum_underSampledGap_le_refined H hH (fun t => (Y t).1))
  rw [integral_finset_sum _ (fun n _ => S.integrable_actual_underSampledGap H n)] at h
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h

/-- Chen et al. JMLR 2016 Theorem 1, with the documented normalized charge repair.
The per-arm gap family is derived from actual bad actions and possible triggers;
an empty family contributes zero. No performance/count premise is assumed. -/
theorem theorem_one_refined_regret (H : ℕ) (hH : 1≤H) :
    S.approximationRegret H ≤ (∑i:Fin m, S.armRefinedTerm H i)+
      (1+(2+(if M.globalMinTrigger<1 then 1 else 0))*Real.pi^2/6)*
        (m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have h := S.approximationRegret_le_underSampled_add_source_tail H
  have hu := S.expected_underSampledGap_le_refined H hH
  calc
    _ ≤ _ := h.trans (add_le_add hu le_rfl)
    _ = _ := by ring

omit [MeasurableSingletonClass A] [StandardBorelSpace A] in
theorem armRefinedTerm_eq_zero_of_no_bad (H : ℕ) (h : ∀a, S.gap a≤0) (i : Fin m) :
    S.armRefinedTerm H i=0 := by
  classical
  have he : ¬(S.badActions i).Nonempty := by
    rintro ⟨a,ha⟩
    exact (not_lt.mpr (h a)) (Finset.mem_filter.mp ha).2.1
  simp [armRefinedTerm,he]

theorem approximationRegret_nonpos_of_no_bad (H : ℕ) (h : ∀a, S.gap a≤0) :
    S.approximationRegret H≤0 := by
  by_cases hH : 1≤H
  · have hr := S.theorem_one_refined_regret H hH
    simpa [S.armRefinedTerm_eq_zero_of_no_bad H h,S.maxPositiveGap_eq_zero_of_no_bad h] using hr
  · have he : H=0 := by omega
    rw [he,S.approximationRegret_zero]

end BanditRLProof.CUCB.SourceModel
