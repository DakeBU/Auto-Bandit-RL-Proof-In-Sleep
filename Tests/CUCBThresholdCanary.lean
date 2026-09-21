import BanditRLProof.Algorithms.CUCBThreshold

/-! Regression for the mixed-p threshold step. This is an algebra canary,
not the frozen noisy CUCB performance canary. -/
namespace Tests.CUCBThresholdCanary
open BanditRLProof.CUCB

private def counts (i : Fin 2) : ℝ := if i = 0 then 7 else 14
private noncomputable def coefficients (i : Fin 2) : ℝ :=
  thresholdCoefficient 1 (if i = 0 then 1 else 1/2)

/-- The old N*p criterion can tie while only one threshold is crossed. -/
theorem mixed_branch_failure :
    (7:ℝ)*1 = 14*(1/2) ∧
    thresholdCoefficient 1 1 < 7 ∧
    ¬ thresholdCoefficient 1 (1/2) < 14 := by
  norm_num [thresholdCoefficient]

/-- The normalized choice must charge the arm still below its threshold. -/
theorem normalized_charge_selects_one :
    normalizedCharge Finset.univ (by simp : (Finset.univ : Finset (Fin 2)).Nonempty)
      counts coefficients = 1 := by
  let i := normalizedCharge Finset.univ
    (by simp : (Finset.univ : Finset (Fin 2)).Nonempty) counts coefficients
  have h := (normalizedCharge_spec Finset.univ
    (by simp : (Finset.univ : Finset (Fin 2)).Nonempty) counts coefficients).2 1
    (Finset.mem_univ _)
  change counts i / coefficients i ≤ counts 1 / coefficients 1 at h
  change i = 1
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with hi | hi
  · rw [hi] at h
    norm_num [counts, coefficients, thresholdCoefficient] at h
  · exact hi

#print axioms thresholdCoefficient_pos
#print axioms normalizedCharge_sufficient
#print axioms exists_threshold_charge
#print axioms normalized_charge_selects_one
end Tests.CUCBThresholdCanary
