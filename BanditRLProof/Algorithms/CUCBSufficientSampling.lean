import BanditRLProof.Algorithms.CUCBThresholdTail
import BanditRLProof.Algorithms.CUCBImpossibleCase

/-! The actual successful-oracle bad-action event after the normalized charged
counter crosses its source threshold. The nice-event and trigger-tail constants
are retained, including the probability-one observation branch. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [StandardBorelSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

def SufficientSuccessfulCharge (H n : ℕ) : Set (ℕ → Round A m) := {Y |
  ∃i, S.chargeData.choose (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1=some i ∧
    samplingThreshold H (S.inverseGap (Y n).1) (M.minTrigger i)<
      (S.chargeData.counters (fun t => (Y t).1) n i : ℝ) ∧
    S.alpha*scoreOptimum S.score (oracleInput (fun t => (Y t).2) n)≤
      S.score (oracleInput (fun t => (Y t).2) n) (Y n).1}

omit [MeasurableSingletonClass A] [StandardBorelSpace A] in
theorem sufficient_successful_charge_subset (H n : ℕ) :
    S.SufficientSuccessfulCharge H n ⊆
      (NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ ∪ ⋃i, S.TriggerShortfall H n i := by
  classical
  intro Y hY
  by_cases hnice : Y∈NiceEvent (fun i => (M.trueInput i:ℝ)) n
  · apply Or.inr
    rcases hY with ⟨i, hi, ht, horacle⟩
    have hbad := (S.chargeData.choose_mem _ _ _ hi).1
    have hgap : 0<S.gap (Y n).1 := by
      simpa [chargeData, FeedbackModel.chargeData, bad] using hbad
    have hcounts := S.chargeData_sufficient _ _ i hi H ht
    have hshort : ∃j∈M.possible (Y n).1,
        (observationCount (fun t => (Y t).2) n j : ℝ)≤
          6*Real.log ((n:ℝ)+1)/(S.inverseGap (Y n).1)^2 := by
      by_contra h
      push Not at h
      exact S.not_bad_of_nice_and_sufficient_observations _ n (Y n).1 hnice horacle h hgap
    obtain ⟨j, hj, hobs⟩ := hshort
    exact Set.mem_iUnion.mpr ⟨j, (Y n).1, hgap, hj, hcounts j hj, hobs⟩
  · exact Or.inl hnice

theorem sufficient_successful_charge_probability (H n : ℕ) (hH : n+1≤H) :
    (cucbTrajectory S.oracle M.environment) (S.SufficientSuccessfulCharge H n) ≤
      ENNReal.ofReal (3*(m:ℝ)/((n:ℝ)+1)^2) := by
  calc
    _ ≤ (cucbTrajectory S.oracle M.environment)
        ((NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ ∪ ⋃i, S.TriggerShortfall H n i) :=
      measure_mono (S.sufficient_successful_charge_subset H n)
    _ ≤ (cucbTrajectory S.oracle M.environment) (NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ +
        (cucbTrajectory S.oracle M.environment) (⋃i, S.TriggerShortfall H n i) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2*(m:ℝ)/((n:ℝ)+1)^2) +
        ENNReal.ofReal ((m:ℝ)/((n:ℝ)+1)^2) :=
      add_le_add (M.nice_event_probability S.oracle n) (S.trigger_shortfall_union_probability H n hH)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

omit [StandardBorelSpace A] in
theorem sufficient_successful_charge_probability_of_all_one (H n : ℕ) (hH : n+1≤H)
    (hp : ∀i, M.minTrigger i=1) :
    (cucbTrajectory S.oracle M.environment) (S.SufficientSuccessfulCharge H n) ≤
      ENNReal.ofReal (2*(m:ℝ)/((n:ℝ)+1)^2) := by
  calc
    _ ≤ (cucbTrajectory S.oracle M.environment)
        ((NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ ∪ ⋃i, S.TriggerShortfall H n i) :=
      measure_mono (S.sufficient_successful_charge_subset H n)
    _ ≤ (cucbTrajectory S.oracle M.environment) (NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ +
        (cucbTrajectory S.oracle M.environment) (⋃i, S.TriggerShortfall H n i) := measure_union_le _ _
    _ = (cucbTrajectory S.oracle M.environment) (NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ := by
      rw [S.trigger_shortfall_union_probability_of_all_one H n hH hp, add_zero]
    _ ≤ _ := M.nice_event_probability S.oracle n

/-- The source indicator uses the minimum of actual trigger probabilities, not
an independent parameter. Nonempty base arms follow from the feasible family. -/
theorem sufficient_successful_charge_probability_source (H n : ℕ) (hH : n+1≤H) :
    (cucbTrajectory S.oracle M.environment) (S.SufficientSuccessfulCharge H n) ≤
      ENNReal.ofReal ((2+(if M.globalMinTrigger<1 then 1 else 0))*(m:ℝ)/((n:ℝ)+1)^2) := by
  classical
  by_cases hp : M.globalMinTrigger<1
  · simpa only [if_pos hp, show (2:ℝ)+1=3 by norm_num] using
      S.sufficient_successful_charge_probability H n hH
  · have heq : M.globalMinTrigger=1 := le_antisymm M.globalMinTrigger_le_one (not_lt.mp hp)
    simpa [hp] using S.sufficient_successful_charge_probability_of_all_one H n hH
      (M.globalMinTrigger_eq_one_iff.mp heq)

end BanditRLProof.CUCB.SourceModel
