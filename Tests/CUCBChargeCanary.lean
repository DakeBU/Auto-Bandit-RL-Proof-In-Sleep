import BanditRLProof.Algorithms.CUCBChargedConcentration

/-! Mixed-trigger regression of the actual integer charging rule.
The final noisy CUCB performance canary remains a separate obligation. -/
namespace Tests.CUCBChargeCanary
open BanditRLProof.CUCB

private noncomputable def rule : ChargeData Bool 2 where
  bad := id
  triggers := fun _ => Finset.univ
  nonempty := fun _ => by simp
  inverseGap := fun _ => 1
  triggerLower := fun i => if i=0 then 1 else 1/2

private def counts (i : Fin 2) : ℕ := if i=0 then 7 else 14

theorem mixed_branch_actual_charge : rule.choose counts true=some 1 := by
  let i := normalizedCharge (rule.triggers true) (rule.nonempty true)
    (fun j => (counts j:ℝ)) (fun j => thresholdCoefficient (rule.inverseGap true) (rule.triggerLower j))
  have h := (normalizedCharge_spec (rule.triggers true) (rule.nonempty true)
    (fun j => (counts j:ℝ)) (fun j => thresholdCoefficient (rule.inverseGap true) (rule.triggerLower j))).2
    1 (by simp [rule])
  change (counts i:ℝ)/thresholdCoefficient 1 (if i=0 then 1 else 1/2) ≤
    (counts 1:ℝ)/thresholdCoefficient 1 (1/2) at h
  have hi : i=1 := by
    have hc : i=0 ∨ i=1 := by omega
    rcases hc with hc | hc
    · rw [hc] at h
      norm_num [counts, thresholdCoefficient] at h
    · exact hc
  change some i=some 1
  rw [hi]

theorem no_bad_actions_no_counter (n : ℕ) (i : Fin 2) :
    rule.counters (fun _ => false) n i=0 := by
  rw [ChargeData.counters_eq_sum]
  simp [ChargeData.choose, rule]

theorem all_bad_actions_counted_once (n : ℕ) :
    ∑i:Fin 2, rule.counters (fun _ => true) n i=n := by
  rw [ChargeData.counters_sum]
  simp [rule]

#print axioms mixed_branch_actual_charge
#print axioms no_bad_actions_no_counter
#print axioms all_bad_actions_counted_once
#print axioms ChargeData.charge_before_feedback
#print axioms ChargeData.measurable_path_charge
#print axioms ChargeData.counters_sum
#print axioms ChargeData.choose_sufficient
#print axioms ChargeData.chargedObservations_le_observationCount
#print axioms integral_triggerFactor_le_one
#print axioms ChargeData.roundKernel_chargedTriggerFactor_le_one
#print axioms ChargeData.cucb_condExp_chargedTriggerFactor
#print axioms ChargeData.cucb_initial_chargedTriggerFactor
#print axioms ChargeData.charged_initial_MGF
#print axioms ChargeData.charged_successor_condMGF
#print axioms ChargeData.charged_count_tail
#print axioms ChargeData.observation_below_charged_half
end Tests.CUCBChargeCanary
