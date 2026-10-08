from common_reviewed_v1 import *

headers_fixed(6)
assert load(RUN / 'all-six-focused-build-v1-exit.json')['exit_code'] == 0
write(CANARY, '''import BanditRLProof.OnlineSquareMinimum
import Mathlib.Tactic

namespace Tests.OnlineSquareMinimum

open BanditRL.OnlineLearning

/-- One fixed infinite target stream; it depends only on time. -/
noncomputable def alternating (t : ℕ) : ℝ := if t % 2 = 0 then 0 else 1

/-- Nonbinary exogenous target stream, again fixed independently of any comparator. -/
noncomputable def quarters (t : ℕ) : ℝ := if t % 2 = 0 then 1 / 4 else 3 / 4

theorem alternating_mem (t : ℕ) : alternating t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold alternating
  split_ifs <;> norm_num

theorem quarters_mem (t : ℕ) : quarters t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold quarters
  split_ifs <;> norm_num

/-- The empty-prefix extension has value zero, without a uniqueness claim. -/
theorem empty_minimum :
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range 0, (u - alternating t)^2) ''
      Set.Icc (0 : ℝ) 1) = 0 := by
  rw [squaredLoss_minimum_eq alternating 0 (by simp)]
  simp

theorem empty_regret : squaredBestRegret alternating (meanPredict alternating) 0 = 0 := by
  rw [squaredBestRegret_eq_comparatorRegret alternating (meanPredict alternating) 0 (by simp)]
  simp [comparatorRegret]

theorem alternating_mean : empiricalMean alternating 2 = 1 / 2 := by
  norm_num [empiricalMean, alternating, Finset.sum_range_succ]

/-- Attainment and the literal real infimum are instantiated on genuinely varying data. -/
theorem alternating_minimum :
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - alternating t)^2) ''
      Set.Icc (0 : ℝ) 1) = 1 / 2 := by
  rw [squaredLoss_minimum_eq alternating 2 (fun t _ => alternating_mem t)]
  norm_num [empiricalMean, alternating, Finset.sum_range_succ]

/-- Existing positive-horizon uniqueness is tested separately, never at zero. -/
theorem alternating_unique (u : ℝ)
    (hu : (∑ t ∈ Finset.range 2, (u - alternating t)^2) ≤
      ∑ t ∈ Finset.range 2, (empiricalMean alternating 2 - alternating t)^2) :
    u = 1 / 2 := by
  exact (empiricalMean_unique alternating 2 (by norm_num) u hu).trans alternating_mean

theorem actual_prediction_values :
    meanPredict alternating 0 = 1 / 2 ∧ meanPredict alternating 1 = 0 ∧
      meanPredict alternating 2 = 1 / 2 := by
  norm_num [meanPredict, empiricalMean, alternating, Finset.sum_range_succ]

theorem actual_regret_one :
    squaredBestRegret alternating (meanPredict alternating) 1 = 1 / 4 := by
  rw [squaredBestRegret_eq_comparatorRegret alternating (meanPredict alternating) 1
    (fun t _ => alternating_mem t)]
  norm_num [comparatorRegret, meanPredict, empiricalMean, alternating, Finset.sum_range_succ]

theorem actual_regret_two :
    squaredBestRegret alternating (meanPredict alternating) 2 = 3 / 4 := by
  rw [squaredBestRegret_eq_comparatorRegret alternating (meanPredict alternating) 2
    (fun t _ => alternating_mem t)]
  norm_num [comparatorRegret, meanPredict, empiricalMean, alternating, Finset.sum_range_succ]

/-- The same time-only prediction stream and a fixed matching target stream give negative regret.
This is a finite pathwise example, not a generic causal learner or an IID excess-risk claim. -/
theorem signed_alternating : squaredBestRegret alternating alternating 2 = -1 / 2 := by
  rw [squaredBestRegret_eq_comparatorRegret alternating alternating 2
    (fun t _ => alternating_mem t)]
  norm_num [comparatorRegret, empiricalMean, alternating, Finset.sum_range_succ]

theorem comparator_zero_order :
    comparatorRegret (fun t x => (x - alternating t)^2) (meanPredict alternating) 0 2 ≤
      squaredBestRegret alternating (meanPredict alternating) 2 := by
  exact comparatorRegret_le_squaredBestRegret alternating (meanPredict alternating) 2
    (fun t _ => alternating_mem t) 0 (by norm_num)

theorem comparator_one_order :
    comparatorRegret (fun t x => (x - alternating t)^2) (meanPredict alternating) 1 2 ≤
      squaredBestRegret alternating (meanPredict alternating) 2 := by
  exact comparatorRegret_le_squaredBestRegret alternating (meanPredict alternating) 2
    (fun t _ => alternating_mem t) 1 (by norm_num)

theorem quarters_mean : empiricalMean quarters 2 = 1 / 2 := by
  norm_num [empiricalMean, quarters, Finset.sum_range_succ]

theorem quarters_minimum :
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - quarters t)^2) ''
      Set.Icc (0 : ℝ) 1) = 1 / 8 := by
  rw [squaredLoss_minimum_eq quarters 2 (fun t _ => quarters_mem t)]
  norm_num [empiricalMean, quarters, Finset.sum_range_succ]

theorem actual_bound :
    squaredBestRegret alternating (meanPredict alternating) 2 ≤ 4 + 4 * Real.log 2 := by
  exact meanPredict_bestRegret_bound alternating 2 (by norm_num) (fun t _ => alternating_mem t)

theorem actual_refined :
    squaredBestRegret alternating (meanPredict alternating) 2 ≤ 9 / 4 := by
  have h := meanPredict_bestRegret_refined alternating 2 (by norm_num) (fun t _ => alternating_mem t)
  norm_num at h
  exact h

theorem actual_refined_one :
    squaredBestRegret alternating (meanPredict alternating) 1 ≤ 1 / 4 := by
  have h := meanPredict_bestRegret_refined alternating 1 (by norm_num) (fun t _ => alternating_mem t)
  norm_num at h
  exact h

/-- Actual reused predictor depends on strictly earlier targets, including its fixed initial half. -/
theorem actual_causality (y z : ℕ → ℝ) (t : ℕ) (h : ∀ i < t, y i = z i) :
    meanPredict y t = meanPredict z t := by
  exact meanPredict_prefix y z t h

theorem actual_identity :
    squaredBestRegret alternating (meanPredict alternating) 2 =
      comparatorRegret (fun t x => (x - alternating t)^2) (meanPredict alternating) (1 / 2) 2 := by
  simpa only [alternating_mean] using
    squaredBestRegret_eq_comparatorRegret alternating (meanPredict alternating) 2
      (fun t _ => alternating_mem t)

end Tests.OnlineSquareMinimum
''')
gate('public-canary-focused-build-v1', 'lake', 'build', 'Tests.OnlineSquareMinimumCanary')
write(RUN / 'public-canary-v1.json', dict(public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    named_canaries=20, time_only_fixtures=2, actual_build='public-canary-focused-build-v1-exit.json',
    meaningful_cases=['Actual attained minimum on 0/1 and nonbinary targets', 'Positive-horizon old uniqueness',
        'Actual first-half strict-past prediction', 'T1/T2 regrets 1/4 and 3/4',
        'Signed time-only example -1/2', 'Feasible comparator ordering', 'Actual rate and exact sharp-tail calls',
        'Empty prefix without uniqueness'],
    IID_expected_minimum_not_proved=True, package_accepted=False, chapter_complete=False, goal_complete=False))
headers_fixed(6)
print('Actual public canary build passed; kernel/source/combined/reader/site gates pending.')
