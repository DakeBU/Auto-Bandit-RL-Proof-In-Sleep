from common_v1 import *
fixed();assert load(RUN/'stabilized-contract-v1.json')['status']=='accepted-with-explicit-delta'
old=MEAN.read_bytes();end=b'end BanditRL.OnlineLearning\r\n' if old.endswith(b'\r\n') else b'end BanditRL.OnlineLearning\n'
assert old.endswith(end)
header=load(CONTRACT/'new-public-headers-v1.json')['empiricalMean_succ']
body=''' := by
  by_cases ht : t = 0
  · subst t
    simp [empiricalMean]
  · have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
    unfold empiricalMean
    rw [Finset.sum_range_succ]
    push_cast
    field_simp
    ring
'''
write(RUN/'leaves/empiricalMean-succ-proof-v1.txt',header+body)
MEAN.write_bytes(old[:-len(end)]+('/-- Exact running-average recurrence, including the empty-prefix transition. -/\n'+header+body+'\n').encode('utf-8')+end)
fixed(proving=True)
gate('focused-Mean-succ-v1','lake','build','BanditRLProof.OnlineLearningMean')
write(RUN/'leaves/Mean-succ-named-v1.lean','import BanditRLProof.OnlineLearningMean\n#check BanditRL.OnlineLearning.empiricalMean_succ\n#print axioms BanditRL.OnlineLearning.empiricalMean_succ\n')
gate('Mean-succ-named-v1','lake','env','lean',RUN/'leaves/Mean-succ-named-v1.lean')
assert 'sorryAx' not in (RUN/'Mean-succ-named-v1.log').read_text(encoding='utf-8')
native('Mean-succ-fence-v1','statement-fence','--declaration',PRE+'empiricalMean_succ','--file',MEAN,'--source-assumption','Structural all-prefix finite-sum mean update, Nat counts; zero case explicit; arbitrary real stream. Not an initialprediction/quarter or cost certificate.','--output',RUN/'native-public-fences/empiricalMean_succ-v1.json')
f=load(RUN/'native-public-fences/empiricalMean_succ-v1.json');assert f['statement']==load(CONTRACT/'stabilized-native-proof-headers-v1.json')['empiricalMean_succ']
native('Mean-succ-safe-v1','safe-verify','--fence',RUN/'native-public-fences/empiricalMean_succ-v1.json','--lean-file',MEAN)
native('Mean-succ-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-STATE-MEAN-SUCC-V1','--statement-hash',f['statement_hash'],'--changed-file',MEAN,'--new-declaration',PRE+'empiricalMean_succ','--lean',MEAN,'--verifier-evidence',RUN/'Mean-succ-named-v1-exit.json','--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual alltime finite-sum recurrence produced; t0 explicit, old4Meanproofs1def retained. Frozen producer terminal remains open; no sourcepackage/chapter acceptance.')
write(RUN/'mean-succ-leaf-compiled-v1.json',dict(status='compiled-leaf',name=PRE+'empiricalMean_succ',statement_hash=f['statement_hash'],public_module_sha256=sha(MEAN),focused_build_exit=load(RUN/'focused-Mean-succ-v1-exit.json')['exit_code'],named_kernel_exit=load(RUN/'Mean-succ-named-v1-exit.json')['exit_code'],native_safe_exit=load(RUN/'Mean-succ-safe-v1-exit.json')['exit_code'],terminal=PRE+'ftlState_eq_predict',terminal_status='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(proving=True);print('First actual dependency-ready leaf compiled; producer terminal still pending.')
