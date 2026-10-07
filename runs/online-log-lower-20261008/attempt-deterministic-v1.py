from common_v1 import *
header=load(CONTRACT/'planned-public-headers-v1.json')['expected_pathRegret_lower']
addition='''
theorem variance_sum (T : ℕ) :
    (∑ t ∈ range T, ((t : ℝ) + 3) / (6 * ((t : ℝ) + 2))) =
      (T : ℝ) / 6 + ((harmonic (T + 1) : ℝ) - 1) / 6 := by
  induction T with
  | zero => norm_num [harmonic]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ]
    push_cast
    have hd : (T : ℝ) + 2 ≠ 0 := by positivity
    field_simp <;> ring

theorem expected_pathLearnerLoss_lower (A : List Bool → ℝ) (T : ℕ) :
    (∑ t ∈ range T, ((t : ℝ) + 3) / (6 * ((t : ℝ) + 2))) ≤
      pathExpectation T (pathLearnerLoss A) := by
  induction T with
  | zero => simp [pathExpectation, pathLearnerLoss]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    exact (add_le_add ih le_rfl).trans (expected_pathLearnerLoss_step A T)

'''+header+''' := by
  have hl := expected_pathLearnerLoss_lower A T
  rw [variance_sum] at hl
  have ho := expected_pathBestLoss T hT
  have eq := pathExpectation_congr T (pathRegret A)
    (fun h => pathLearnerLoss A h - pathBestLoss h)
    (fun h _ => pathRegret_eq_losses A h)
  rw [eq, pathExpectation_sub, ho]
  linarith
'''
ending='end BanditRL.OnlineLearning.GuessingLower';source=PUBLIC.read_text(encoding='utf-8')
write(RUN/'deterministic-addition-v1.lean.txt',addition)
write(RUN/'leaves/deterministic-v1.lean',source[:source.rindex(ending)]+addition+'\n'+ending+'\n')
gate('deterministic-attempt-v1','lake','env','lean',RUN/'leaves/deterministic-v1.lean')
