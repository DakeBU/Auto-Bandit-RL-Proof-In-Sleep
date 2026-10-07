from common_v1 import *
fixed(proving=True)
defs=load(CONTRACT/'production-definitions-v1.json');headers=load(CONTRACT/'new-public-headers-v1.json')
assert load(RUN/'state-definition-bindings-v1.json')['recursive_identity_method'].startswith('Actual whole-function equality')
bodies={
'ftlPredict_prefix':''' := by
  unfold ftlPredict empiricalMean
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact h i (Finset.mem_range.mp hi)
''',
'ftlPredict_mem':''' := by
  unfold ftlPredict
  split_ifs with h
  · exact hi
  · exact empiricalMean_mem y t (Nat.pos_of_ne_zero h) hy
''',
'ftlPredict_half':''' := by
  rfl
''',
'ftlState_first':''' := by
  simp [ftlState, ftlMeanStep]
''',
'ftlState_eq_predict':''' := by
  induction t with
  | zero => simp [ftlState, ftlPredict]
  | succ t ih =>
    by_cases ht : t = 0
    · subst t
      simpa [ftlPredict, empiricalMean] using ftlState_first initial y
    · rw [ftlState, ih]
      apply Prod.ext
      · rfl
      · simpa [ftlMeanStep, ftlPredict, ht] using (empiricalMean_succ y t).symm
''',
'ftlState_prefix':''' := by
  rw [ftlState_eq_predict initial y t, ftlState_eq_predict initial z t,
    ftlPredict_prefix initial y z t h]
''',
'ftlState_mem':''' := by
  rw [ftlState_eq_predict]
  exact ftlPredict_mem initial y t hi hy
''',
'ftlState_half':''' := by
  rw [ftlState_eq_predict, ftlPredict_half]
'''}
rows=[]
for n,body in bodies.items():
 if n=='ftlPredict_prefix':
  f=load(RUN/'native-public-fences/ftlPredict_prefix-v2.json');rows.append(dict(name=PRE+n,statement_hash=f['statement_hash'],focused_exit=0,safe_exit=0));continue
 old=PUBLIC.read_bytes();end=b'end BanditRL.OnlineLearning\n';assert old.endswith(end)
 write(RUN/'leaves'/(n+'-proof-v1.txt'),headers[n]+body)
 PUBLIC.write_bytes(old[:-len(end)]+(headers[n]+body+'\n').encode()+end)
 fixed(proving=True)
 gate('focused-'+n+'-v1','lake','build','BanditRLProof.OnlineLearningFTLState')
 native('fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--source-assumption',headers[n],'--output',RUN/'native-public-fences'/(n+'-v1.json'))
 f=load(RUN/'native-public-fences'/(n+'-v1.json'));assert f['statement']==load(CONTRACT/'stabilized-native-proof-headers-v1.json')[n]
 native('safe-'+n+'-v1','safe-verify','--fence',RUN/'native-public-fences'/(n+'-v1.json'),'--lean-file',PUBLIC)
 native('trial-'+n+'-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-STATE-'+n+'-V1','--statement-hash',f['statement_hash'],'--changed-file',PUBLIC,'--new-declaration',PRE+n,'--lean',PUBLIC,'--verifier-evidence',RUN/('focused-'+n+'-v1-exit.json'),'--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual dependency-ready state leaf compiled at exact frozen header; no sourcepackage/Chapter acceptance.')
 rows.append(dict(name=PRE+n,statement_hash=f['statement_hash'],focused_exit=0,safe_exit=0))
write(RUN/'state-body-leaves-compiled-v1.json',dict(status='Actual8 state proof bodies compiled incrementally; central producer terminal closed locally',rows=rows,public_sha256=sha(PUBLIC),mean_sha256=sha(MEAN),central_terminal=PRE+'ftlState_eq_predict',central_terminal_status='compiled-local',definitions_raw_and_compiled_rfl_verified=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(proving=True);print('Actual producer terminal locally closed; canary/BODY/combined/reader gates pending.')
