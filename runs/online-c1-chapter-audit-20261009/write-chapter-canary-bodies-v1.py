from common_proving_v2 import *
fixed()
spec=load(CONTRACT/'chapter-canary-targets-stabilized-v1.json')
bodies={
'C001':r'''  have h : squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 = 1 := by
    rw [squaredBestRegret_eq_comparatorRegret _ _ _ (by intros; norm_num)]
    norm_num [comparatorRegret, ftlPredict, empiricalMean, Finset.sum_range_succ]
  exact ⟨h, by rw [h]; norm_num⟩''',
'C002':r'''  have h := ftlPredict_bestRegret_initial_correction 0 falling 2 (by omega)
  norm_num [falling] at h
  exact h''',
'C003':r'''  refine ⟨?_, ?_, ?_⟩
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (fun t _ => rising_mem t)]
    norm_num [comparatorRegret, ftlPredict, empiricalMean, rising, Finset.sum_range_succ]
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (fun t _ => rising_mem t)]
    norm_num [comparatorRegret, meanPredict, empiricalMean, rising, Finset.sum_range_succ]
  · norm_num [rising]''',
'C004':r'''  refine ⟨?_, ?_, ?_⟩
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (fun t _ => falling_mem t)]
    norm_num [comparatorRegret, ftlPredict, empiricalMean, falling, Finset.sum_range_succ]
  · have h := ftlPredict_bestRegret_refined 0 falling 2 (by omega) (by norm_num)
      (fun t _ => falling_mem t)
    norm_num [Finset.sum_range_succ] at h
    exact h
  · have h := ftlPredict_bestRegret_refined 0 (fun _ => (1 : ℝ)) 1 (by omega)
      (by norm_num) (by intros; norm_num)
    norm_num at h
    exact h''',
'C005':r'''  refine ⟨?_, ?_, ?_⟩
  · apply ftlState_prefix
    intro i hi
    have : i = 0 := by omega
    subst i
    norm_num [rising]
  · norm_num [rising]
  · norm_num [ftlState_eq_predict, ftlPredict, empiricalMean, rising, Finset.sum_range_succ]''',
'C006':r'''  refine ⟨rfl, ?_, ?_⟩
  · rw [ftlState_first]
    norm_num [rising]
  · rw [ftlState_eq_predict]
    norm_num [ftlPredict, empiricalMean, rising, Finset.sum_range_succ]''',
'C007':r'''  intro initial hi
  exact ftlPredict_upperNoRegret initial dyadicObservation hi dyadicObservation_unit''',
'C008':r'''  exact ftlPredict_bestRegret_average_tendsto_zero ((3 : ℝ) / 4) dyadicObservation
    (by norm_num) dyadicObservation_unit''',
'C009':r'''  have h := ftlPredict_bestRegret_initial_correction 2 (fun _ => (3 : ℝ)) 1 (by omega)
  norm_num at h
  linarith''',
'C010':r'''  refine ⟨?_, ?_, ?_⟩
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (by intros; omega)]
    simp [comparatorRegret]
  · rw [squaredBestRegret_eq_comparatorRegret _ _ _ (by intros; omega)]
    simp [comparatorRegret]
  · norm_num [falling]''',
'C011':r'''  refine ⟨?_, general_initial_finite_values.1⟩
  norm_num [comparatorRegret, ftlPredict, empiricalMean, falling, Finset.sum_range_succ]''',
'C012':r'''  refine ⟨observation_variance 0, meanPredict_two_round_excess, ?_⟩
  rw [meanPredict_two_round_excess]
  norm_num''',
'C013':r'''  exact ⟨actual_mean_attainment, constant_known_mean_zero 2⟩''',
'C014':r'''  exact ⟨hindsight_minimum_two, two_round_fixed_minimum⟩''',
'C015':r'''  exact Tests.OnlineGuessingIIDSuccess.actual_meanPredict_success''',
'C016':r'''  have h := RegretDomainsProbe.outside_prediction_and_negative_regret
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  norm_num [comparatorRegret, RegretDomainsProbe.domainLoss, RegretDomainsProbe.output,
    RegretDomainsProbe.referenceOne, Finset.sum_range_succ]''',
'C017':r'''  refine ⟨?_, ?_, ?_⟩
  · norm_num [empiricalMean, rising, Finset.sum_range_succ]
  · rw [squaredLoss_minimum_eq rising 2 (fun t _ => rising_mem t)]
    norm_num [empiricalMean, rising, Finset.sum_range_succ]
  · intros
    simp''',
'C018':r'''  intro u hu
  exact (empiricalMean_unique rising 2 (by omega) u hu).trans
    produced_minimum_and_empty_nonunique.1''',
'C019':r'''  refine ⟨?_, ?_, ?_⟩
  · norm_num [ChapterOneCase0.demoLoss, ChapterOneCase0.demoLeader, Finset.sum_range_succ]
  · norm_num [ChapterOneCase0.demoLoss, ChapterOneCase0.demoLeader, Finset.sum_range_succ]
  · apply lemma_1_2 Set.univ ChapterOneCase0.demoLoss ChapterOneCase0.demoLeader 2
    · simp
    · intro n hn hnt u hu
      interval_cases n <;> cases u <;>
        norm_num [ChapterOneCase0.demoLoss, ChapterOneCase0.demoLeader, Finset.sum_range_succ]''',
'C020':r'''  refine ⟨positive_regret_negative_correction.2.1, ?_, ?_⟩
  · have h := meanPredict_bestRegret_refined rising 2 (by omega) (fun t _ => rising_mem t)
    norm_num [Finset.sum_range_succ] at h
    exact h
  · exact meanPredict_bestRegret_bound rising 2 (by omega) (fun t _ => rising_mem t)''',
'C021':r'''  refine ⟨?_, ?_⟩
  · norm_num [meanPredict, empiricalMean, rising, Finset.sum_range_succ]
  · change (meanPredict rising 1 - rising 1)^2 - (empiricalMean rising 2 - rising 1)^2 ≤
      4 / ((1 : ℝ) + 1)
    exact meanPredict_stability rising 1 (fun i _ => rising_mem i)''',
'C022':r'''  exact ⟨Tests.OnlineGuessingKernelCausal.every_horizon_excess,
    Tests.OnlineGuessingKernelCausal.history_feedback_distribution.1,
    Tests.OnlineGuessingKernelCausal.history_feedback_distribution.2.1⟩''',
'C023':r'''  exact ⟨Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_negative_two,
    meanPredict_two_round_excess⟩''',
'C024':r'''  exact dyadic_meanPredict_obstruction''',
'C025':r'''  exact GuessingLogLowerProbe.seeded_log_endpoint''',
'C026':r'''  refine ⟨?_, harmonic_le_one_add_log 2⟩
  norm_num [harmonic, Finset.sum_range_succ]''',
'C027':r'''  exact ⟨Tests.OnlineGuessingIIDSuccess.nonzero_initial_total_sublinear, by norm_num⟩'''
}
helpers=r'''private theorem rising_mem (t : ℕ) : rising t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold rising
  split_ifs <;> norm_num

private theorem falling_mem (t : ℕ) : falling t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold falling
  split_ifs <;> norm_num

'''
assert set(bodies)=={t['id'] for t in spec['targets']}
value=spec['setup']+helpers+'\n\n'.join(t['header']+' := by\n'+bodies[t['id']] for t in spec['targets'])+'\n\nend Tests.OnlineLearningChapterAudit\n'
write(ROOT/'Tests/OnlineLearningChapterAuditCanary.lean',value)
fixed()
print('Wrote exact27 actual canary bodies; frozen types preserved; no integration/acceptance claim.')
