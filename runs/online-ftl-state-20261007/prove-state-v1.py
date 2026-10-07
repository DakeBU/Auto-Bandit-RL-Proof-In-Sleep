from common_v1 import *
fixed(proving=True);assert load(RUN/'mean-succ-leaf-compiled-v1.json')['status']=='compiled-leaf'
defs=load(CONTRACT/'production-definitions-v1.json');headers=load(CONTRACT/'new-public-headers-v1.json')
prefix='import BanditRLProof.OnlineLearningFTL\n\nnamespace BanditRL.OnlineLearning\n\n'
prefix += '\n\n'.join(defs.values())+'\n\n'
write(PUBLIC,prefix+'end BanditRL.OnlineLearning\n')
write(RUN/'leaves/state-definitions-frozen-v1.txt',prefix)
gate('focused-state-definitions-v1','lake','build','BanditRLProof.OnlineLearningFTLState')
neutral=(RUN/'leaves/neutral-closed-props-v1.lean').read_text(encoding='utf-8')
identities='import BanditRLProof.OnlineLearningFTLState\n'+neutral+'\n'
identities += 'example : Neutral.a = BanditRL.OnlineLearning.empiricalMean := by rfl\n'
for a,n in [('b','ftlPredict'),('c','ftlMeanStep'),('d','ftlState')]:identities += f'example : Neutral.{a} = {PRE+n} := by rfl\n'
for n in defs:identities += '#check '+PRE+n+'\n#print axioms '+PRE+n+'\n'
write(RUN/'leaves/state-definition-identities-v1.lean',identities)
gate('state-definition-identities-v1','lake','env','lean',RUN/'leaves/state-definition-identities-v1.lean')
assert 'sorryAx' not in (RUN/'state-definition-identities-v1.log').read_text(encoding='utf-8')
write(RUN/'state-definition-bindings-v1.json',dict(status='Actual3 new definitions + canonicalMean neutral rfl identities compiled; actual new3 names/types/kernel checked',full_definition_rows=[dict(name=PRE+n,source_raw_text=h,sha256=hashlib.sha256(h.encode()).hexdigest()) for n,h in defs.items()],actual_module_definition_prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),recursive_native_fence_claim=False,native_api_boundary='Equation-style recursion is not supported by native header extractor; exact full raw definition and compiled identities/types/kernel are separate actual evidence',source_package_accepted=False))
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
 old=PUBLIC.read_bytes();end=b'end BanditRL.OnlineLearning\n';assert old.endswith(end)
 write(RUN/'leaves'/(n+'-proof-v1.txt'),headers[n]+body)
 PUBLIC.write_bytes(old[:-len(end)]+(headers[n]+body+'\n').encode()+end)
 fixed(proving=True)
 gate('focused-'+n+'-v1','lake','build','BanditRLProof.OnlineLearningFTLState')
 native('fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--source-assumption','Frozen CONTRACT general-initial FTL causal state refinement; see source contract for exact initial/prefix/real-arithmetic boundary.','--output',RUN/'native-public-fences'/(n+'-v1.json'))
 f=load(RUN/'native-public-fences'/(n+'-v1.json'));assert f['statement']==load(CONTRACT/'stabilized-native-proof-headers-v1.json')[n]
 native('safe-'+n+'-v1','safe-verify','--fence',RUN/'native-public-fences'/(n+'-v1.json'),'--lean-file',PUBLIC)
 native('trial-'+n+'-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-STATE-'+n+'-V1','--statement-hash',f['statement_hash'],'--changed-file',PUBLIC,'--new-declaration',PRE+n,'--lean',PUBLIC,'--verifier-evidence',RUN/('focused-'+n+'-v1-exit.json'),'--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual dependency-ready state leaf compiled at exact frozen header; no sourcepackage/Chapter acceptance.')
 rows.append(dict(name=PRE+n,statement_hash=f['statement_hash'],focused_exit=0,safe_exit=0))
write(RUN/'state-body-leaves-compiled-v1.json',dict(status='Actual8 state proof bodies compiled incrementally; central producer terminal closed locally',rows=rows,public_sha256=sha(PUBLIC),mean_sha256=sha(MEAN),central_terminal=PRE+'ftlState_eq_predict',central_terminal_status='compiled-local',definitions_raw_and_compiled_rfl_verified=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(proving=True);print('Actual producer terminal locally closed; canary/BODY/combined/reader gates pending.')
