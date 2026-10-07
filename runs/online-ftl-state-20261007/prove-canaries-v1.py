from common_v1 import *
fixed(proving=True);assert load(RUN/'state-body-leaves-compiled-v1.json')['central_terminal_status']=='compiled-local'
headers=load(CONTRACT/'planned-canary-headers-v1.json')
defs=load(CONTRACT/'test-definition-v1.json')
bodies={
'initial_and_first':''' := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simpa using ftlState_first 0 (fun _ => (1 : ℝ))
  · simpa using ftlState_first 1 (fun _ => (1 : ℝ))
''',
'varying_updates':''' := by
  constructor
  · rw [ftlState_eq_predict]
    norm_num [ftlPredict, empiricalMean, probeTargets, Finset.sum_range_succ]
  · rw [ftlState_eq_predict]
    norm_num [ftlPredict, empiricalMean, probeTargets, Finset.sum_range_succ]
''',
'current_target_after_prediction':''' := by
  refine ⟨?_, ?_, ?_⟩
  · apply ftlState_prefix
    intro i hi
    have hz : i = 0 := by omega
    subst i
    rfl
  · norm_num [probeTargets]
  · norm_num [ftlState_eq_predict, ftlPredict, empiricalMean, probeTargets,
      Finset.sum_range_succ]
''',
'feasibility_and_outside':''' := by
  refine ⟨ftlState_mem 1 probeTargets 2 (by norm_num) ?_, ?_, ?_⟩
  · intro i hi
    unfold probeTargets
    split_ifs <;> norm_num
  · norm_num [ftlState]
  · rw [ftlState_first]
    rfl
''',
'half_state_regret':''' := by
  constructor
  · simp only [ftlState_half, Prod.snd]
    norm_num [meanPredict, empiricalMean, probeTargets, Finset.sum_range_succ]
  · simp only [ftlState_half, Prod.snd]
    exact meanPredict_regret_refined probeTargets 2 (by norm_num) (by
      intro i hi
      unfold probeTargets
      split_ifs <;> norm_num)
''',
'general_initial_not_quarter':''' := by
  refine ⟨ftlState_mem 1 (fun _ => 0) 0 (by norm_num) (by intro i hi; omega), ?_, ?_⟩
  · norm_num [ftlState]
  · norm_num [ftlState]
'''}
text='import BanditRLProof.OnlineLearningFTLState\n\nopen BanditRL.OnlineLearning\nnamespace FTLStateProbe\n\n'+defs['probeTargets']+'\n\n'
text += '\n\n'.join(headers[n]+body for n,body in bodies.items())+'\nend FTLStateProbe\n'
write(CANARY,text);write(RUN/'leaves/canary-bodies-v1.txt',text)
gate('focused-canaries-v1','lake','build','Tests.OnlineLearningFTLStateCanary')
native('canaries-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-STATE-CANARIES-V1','--changed-file',CANARY,'--lean',CANARY,'--verifier-evidence',RUN/'focused-canaries-v1-exit.json','--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual six validation proofs instantiate produced state/generalinitial/causality/feasibility/half sourcebound with changing target and counterexamples; not six bookresults. BODY/combined/reader/source acceptance pending.')
write(RUN/'canaries-compiled-v1.json',dict(status='Actual6 named validation proof bodies compiled',canary_sha256=sha(CANARY),named_validation_proofs=6,test_definitions=1,source_subobligation_count=2,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(proving=True)
