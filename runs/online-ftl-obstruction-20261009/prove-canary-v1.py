from common_canary_v1 import *
s=canary_contract_fixed();assert not CANARY.exists()
targets=load(CONTRACT/'canary-targets-v1.json')['targets']
bodies=[
'''  refine ⟨dyadicObservation_unit, ?_⟩
  norm_num [dyadicObservation]
''',
'''  norm_num [meanPredict, empiricalMean, dyadicObservation, Finset.sum_range_succ]
''',
'''  have heq (T : ℕ) := squaredBestRegret_eq_comparatorRegret dyadicObservation
    (meanPredict dyadicObservation) T (fun t _ => dyadicObservation_unit t)
  rw [heq 0, heq 1, heq 2, heq 3]
  norm_num [comparatorRegret, meanPredict, empiricalMean, dyadicObservation, Finset.sum_range_succ]
''',
'''  exact meanPredict_limitNoRegret_iff_mean_converges dyadicObservation dyadicObservation_unit
''',
'''  intro h
  exact dyadic_meanPredict_obstruction.2.2.2 (all_comparator_iff_instantiated.mpr h)
''',
'''  exact dyadic_empiricalMean_subsequences
''',
'''  exact dyadic_meanPredict_obstruction
''',
'''  exact dyadic_meanPredict_obstruction.1
''',
'''  exact dyadic_meanPredict_obstruction.2.1
''',
'''  exact dyadic_meanPredict_obstruction.2.2.1
''',
'''  exact dyadic_meanPredict_obstruction.2.2.2
''']
assert len(targets)==len(bodies)==11
prefix=(CONTRACT/'canary-context-v1.lean.txt').read_text(encoding='utf8').rsplit('end Tests.OnlineFTLOscillation',1)[0]
write(CANARY,prefix+'\n'+'\n\n'.join(t['header']+' := by\n'+b.rstrip() for t,b in zip(targets,bodies))+
    '\n\nend Tests.OnlineFTLOscillation\n')
canary_contract_fixed();write(RUN/'canary-attempt-v1.lean.raw',CANARY.read_bytes())
code=gate('canary-focused-v1','lake','build','Tests.OnlineFTLOscillationCanary',required=False)
write(RUN/'canary-attempt-v1.json',dict(frozen_targets=11,actual_build_exit=code,
    status='compiled' if code==0 else 'repair',source_sha256=sha(CANARY),package_accepted=False,chapter_complete=False,goal_complete=False))
gate('canary-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
    '--task',TASK,'--role','lower','--kind','attempt','--status','compiled' if code==0 else 'failed',
    '--run-id',RUN.name,'--lean',CANARY.relative_to(ROOT).as_posix(),'--attempt-id','canary-v1',
    '--verifier-evidence',RUN/'canary-focused-v1-exit.json',
    '--notes','Actual dyadic same-FTL eleven public canaries with reviewed immutable headers; BODY/full gates pending.',
    '--progress-class','unreviewed','--obligations-before','4','--obligations-after','4')
assert code==0,'Retain failed canary; repair proof only with exact frozen terminals.'
