from common_canary_v1 import *
s=canary_contract_fixed()
assert not CANARY.exists()
targets=load(CONTRACT/'canary-targets-v1.json')['targets']
bodies=[
'''  refine ⟨?_, ?_, ?_⟩
  · intro t
    unfold alternatingObservation
    split_ifs <;> norm_num
  · norm_num [alternatingObservation]
  · norm_num [alternatingObservation]
''',
'''  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : n % 2 = 0
    · have hdiv : (n + 1) / 2 = n / 2 := by omega
      simp [alternatingObservation, hn, hdiv]
    · have hdiv : (n + 1) / 2 = n / 2 + 1 := by omega
      simp [alternatingObservation, hn, hdiv, Nat.cast_add]
''',
'''  have hbounds : ∀ᶠ T : ℕ in atTop,
      0 ≤ (1 : ℝ) / 2 - empiricalMean alternatingObservation T ∧
      (1 : ℝ) / 2 - empiricalMean alternatingObservation T ≤ 1 / (T : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    have hcount : ((T / 2 : ℕ) : ℝ) * 2 + ((T % 2 : ℕ) : ℝ) = (T : ℝ) := by
      exact_mod_cast (show T / 2 * 2 + T % 2 = T by omega)
    have hrem : (0 : ℝ) ≤ ((T % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrem1 : ((T % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast (show T % 2 ≤ 1 by omega)
    rw [empiricalMean, alternating_prefix_sum]
    constructor
    · apply sub_nonneg.mpr
      apply (div_le_iff₀ hTR).mpr
      nlinarith
    · apply (le_div_iff₀ hTR).mpr
      have hid : ((1 : ℝ) / 2 - ((T / 2 : ℕ) : ℝ) / (T : ℝ)) * (T : ℝ) =
          (T : ℝ) / 2 - ((T / 2 : ℕ) : ℝ) := by field_simp
      rw [hid]
      nlinarith
  have hinv : Tendsto (fun T : ℕ => (1 : ℝ) / (T : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hdiff : Tendsto (fun T : ℕ => (1 : ℝ) / 2 - empiricalMean alternatingObservation T)
      atTop (nhds 0) := squeeze_zero' (hbounds.mono (fun _ h => h.1))
        (hbounds.mono (fun _ h => h.2)) hinv
  have hres := (tendsto_const_nhds (x := (1 : ℝ) / 2)).sub hdiff
  simpa only [sub_zero, sub_sub_cancel] using hres
''',
'''  norm_num [meanPredict, empiricalMean, alternatingObservation, Finset.sum_range_succ]
''',
'''  have heq (T : ℕ) := squaredBestRegret_eq_comparatorRegret alternatingObservation
    (meanPredict alternatingObservation) T (fun t _ => alternating_unit.1 t)
  rw [heq 0, heq 1, heq 2]
  norm_num [comparatorRegret, meanPredict, empiricalMean, alternatingObservation, Finset.sum_range_succ]
''',
'''  exact meanPredict_bestLoss_nonneg alternatingObservation T
''',
'''  exact meanPredict_comparator_decomposition alternatingObservation u T
''',
'''  exact meanPredict_bestRegret_average_tendsto_zero alternatingObservation alternating_unit.1
''',
'''  exact meanPredict_fixedRegret_limit_iff alternatingObservation alternating_unit.1 u a
''',
'''  have h := (meanPredict_limitNoRegret_of_mean_converges alternatingObservation
    alternating_unit.1 ((1 : ℝ) / 2) alternating_mean_tendsto).1 0
  norm_num at h ⊢
  exact h
''',
'''  have h := (meanPredict_limitNoRegret_of_mean_converges alternatingObservation
    alternating_unit.1 ((1 : ℝ) / 2) alternating_mean_tendsto).1 ((1 : ℝ) / 2)
  simpa using h
''',
'''  exact (meanPredict_limitNoRegret_of_mean_converges alternatingObservation
    alternating_unit.1 ((1 : ℝ) / 2) alternating_mean_tendsto).2
''']
prefix=(CONTRACT/'canary-context-v1.lean.txt').read_text(encoding='utf8').rsplit('end Tests.OnlineFTLLimitSemantics',1)[0]
write(CANARY,prefix+'\n'+'\n\n'.join(t['header']+' := by\n'+b.rstrip() for t,b in zip(targets,bodies))+
    '\n\nend Tests.OnlineFTLLimitSemantics\n')
canary_contract_fixed()
write(RUN/'canary-attempt-v1.lean.raw',CANARY.read_bytes())
code=gate('canary-focused-v1','lake','build','Tests.OnlineFTLLimitSemanticsCanary',required=False)
write(RUN/'canary-attempt-v1.json',dict(frozen_targets=12,actual_build_exit=code,
    status='compiled' if code==0 else 'repair',source_sha256=sha(CANARY),package_accepted=False,chapter_complete=False,goal_complete=False))
gate('canary-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
    '--task',TASK,'--role','lower','--kind','attempt','--status','compiled' if code==0 else 'failed',
    '--run-id',RUN.name,'--lean',CANARY.relative_to(ROOT).as_posix(),'--attempt-id','canary-v1',
    '--verifier-evidence',(RUN/'canary-focused-v1-exit.json').as_posix(),
    '--notes','Actual binary same-FTL canary build; exact12 reviewed headers preserved. Semantic body review still required.',
    '--progress-class','unreviewed','--obligations-before','5','--obligations-after','5')
assert code==0,'Failed canary body retained; repair body without terminal edits.'
print('12 exact public canary bodies focused-compiled; full acceptance pending.',flush=True)
