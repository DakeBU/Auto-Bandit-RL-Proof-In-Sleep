import BanditRLProof.Algorithms.CUCBRegretDecomposition
import Mathlib.NumberTheory.ZetaValues

/-! Exact cumulative source tail and signed regret reduction to the actual
under-sampled charge weight. The refined gap integral remains separate. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [StandardBorelSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

theorem expected_sufficientIndicator_le (H n : ℕ) (hH : n+1≤H) :
    (∫Y, S.sufficientIndicator H n Y ∂cucbTrajectory S.oracle M.environment) ≤
      (2+(if M.globalMinTrigger<1 then 1 else 0))*(m:ℝ)/((n:ℝ)+1)^2 := by
  classical
  have he : (∫Y, S.sufficientIndicator H n Y ∂cucbTrajectory S.oracle M.environment)=
      ((cucbTrajectory S.oracle M.environment) (S.SufficientSuccessfulCharge H n)).toReal := by
    simpa only [Set.indicator_apply, sufficientIndicator, measureReal_def] using
      (integral_indicator_one (μ:=cucbTrajectory S.oracle M.environment)
        (S.measurableSet_sufficientSuccessfulCharge H n))
  rw [he]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (S.sufficient_successful_charge_probability_source H n hH)
  rw [ENNReal.toReal_ofReal (by split_ifs <;> positivity)] at h
  exact h

theorem sum_inverse_square_le (H : ℕ) :
    (∑n∈Finset.range H, (((n:ℝ)+1)^2)⁻¹)≤Real.pi^2/6 := by
  have h := sum_le_hasSum (Finset.range (H+1))
    (fun n _ => by positivity : ∀n∉Finset.range (H+1), 0≤(1:ℝ)/(n:ℝ)^2) hasSum_zeta_two
  simpa [Finset.sum_range_succ', one_div, Nat.cast_add, Nat.cast_one] using h

theorem sum_expected_sufficientIndicator_le (H : ℕ) :
    (∑n∈Finset.range H, ∫Y, S.sufficientIndicator H n Y ∂cucbTrajectory S.oracle M.environment) ≤
      (2+(if M.globalMinTrigger<1 then 1 else 0))*(m:ℝ)*(Real.pi^2/6) := by
  have h := Finset.sum_le_sum (s:=Finset.range H) (fun n hn =>
    S.expected_sufficientIndicator_le H n (Nat.succ_le_of_lt (Finset.mem_range.mp hn)))
  simp only [div_eq_mul_inv, ← Finset.mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_left (sum_inverse_square_le H) (by split_ifs <;> positivity))

/-- The original signed regret, with the oracle-failure credit cancelled and
all sufficiently sampled rounds summed with the exact source constant. -/
theorem approximationRegret_le_underSampled_add_source_tail (H : ℕ) :
    S.approximationRegret H ≤
      (∑n∈Finset.range H, ∫Y : ℕ → Round A m, S.underSampledGap H
        (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1 ∂cucbTrajectory S.oracle M.environment) +
      (2+(if M.globalMinTrigger<1 then 1 else 0))*(m:ℝ)*
        maxPositiveGap S.score M.trueInput S.alpha*Real.pi^2/6 := by
  have h := S.approximationRegret_le_underSampled_add_sufficient H
  have ht := mul_le_mul_of_nonneg_left (S.sum_expected_sufficientIndicator_le H)
    S.maxPositiveGap_nonneg
  calc
    _ ≤ _ := h.trans (add_le_add le_rfl ht)
    _ = _ := by ring

end BanditRLProof.CUCB.SourceModel
