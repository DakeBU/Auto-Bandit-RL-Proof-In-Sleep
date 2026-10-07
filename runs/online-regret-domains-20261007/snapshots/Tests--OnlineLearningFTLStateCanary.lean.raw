import BanditRLProof.OnlineLearningFTLState

open BanditRL.OnlineLearning
namespace FTLStateProbe

def probeTargets (t : ℕ) : ℝ := if t = 0 then 0 else 1

theorem initial_and_first :
    ftlState 0 (fun _ => 1) 0 = (0, 0) ∧
    ftlState 1 (fun _ => 1) 0 = (0, 1) ∧
    ftlState 0 (fun _ => 1) 1 = (1, 1) ∧
    ftlState 1 (fun _ => 1) 1 = (1, 1) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simpa using ftlState_first 0 (fun _ => (1 : ℝ))
  · simpa using ftlState_first 1 (fun _ => (1 : ℝ))


theorem varying_updates :
    ftlState ((3 : ℝ) / 4) probeTargets 2 = (2, (1 : ℝ) / 2) ∧
    ftlState ((3 : ℝ) / 4) probeTargets 3 = (3, (2 : ℝ) / 3) := by
  constructor
  · rw [ftlState_eq_predict]
    norm_num [ftlPredict, empiricalMean, probeTargets, Finset.sum_range_succ]
  · rw [ftlState_eq_predict]
    norm_num [ftlPredict, empiricalMean, probeTargets, Finset.sum_range_succ]


theorem current_target_after_prediction :
    ftlState 0 (fun _ => 0) 1 = ftlState 0 probeTargets 1 ∧
    (0 : ℝ) ≠ probeTargets 1 ∧
    ftlState 0 (fun _ => 0) 2 ≠ ftlState 0 probeTargets 2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply ftlState_prefix
    intro i hi
    have hz : i = 0 := by omega
    subst i
    rfl
  · norm_num [probeTargets]
  · norm_num [ftlState_eq_predict, ftlPredict, empiricalMean, probeTargets,
      Finset.sum_range_succ]


theorem feasibility_and_outside :
    (ftlState 1 probeTargets 2).2 ∈ Set.Icc (0 : ℝ) 1 ∧
    (ftlState 2 probeTargets 0).2 ∉ Set.Icc (0 : ℝ) 1 ∧
    (ftlState 2 probeTargets 1).2 = 0 := by
  refine ⟨ftlState_mem 1 probeTargets 2 (by norm_num) ?_, ?_, ?_⟩
  · intro i hi
    unfold probeTargets
    split_ifs <;> norm_num
  · norm_num [ftlState]
  · rw [ftlState_first]
    rfl


theorem half_state_regret :
    ((∑ t ∈ Finset.range 2, ((ftlState ((1 : ℝ) / 2) probeTargets t).2 - probeTargets t)^2) -
      (∑ t ∈ Finset.range 2, (empiricalMean probeTargets 2 - probeTargets t)^2)) = (3 : ℝ) / 4 ∧
    ((∑ t ∈ Finset.range 2, ((ftlState ((1 : ℝ) / 2) probeTargets t).2 - probeTargets t)^2) -
      (∑ t ∈ Finset.range 2, (empiricalMean probeTargets 2 - probeTargets t)^2)) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2) := by
  constructor
  · simp only [ftlState_half, Prod.snd]
    norm_num [meanPredict, empiricalMean, probeTargets, Finset.sum_range_succ]
  · simp only [ftlState_half, Prod.snd]
    exact meanPredict_regret_refined probeTargets 2 (by norm_num) (by
      intro i hi
      unfold probeTargets
      split_ifs <;> norm_num)


theorem general_initial_not_quarter :
    (ftlState 1 (fun _ => 0) 0).2 ∈ Set.Icc (0 : ℝ) 1 ∧
    ((ftlState 1 (fun _ => 0) 0).2 - 0)^2 = 1 ∧
    ((ftlState 1 (fun _ => 0) 0).2 - 0)^2 > (1 : ℝ) / 4 := by
  refine ⟨ftlState_mem 1 (fun _ => 0) 0 (by norm_num) (by intro i hi; omega), ?_, ?_⟩
  · norm_num [ftlState]
  · norm_num [ftlState]

end FTLStateProbe
