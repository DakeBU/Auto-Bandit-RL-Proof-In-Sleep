from common_proving_v1 import *
s=proving_fixed()
assert not PUBLIC.exists()
prefix=(CONTRACT/'context-v1.lean.txt').read_text(encoding='utf8').rsplit('end BanditRL.OnlineLearning',1)[0]
body=''' := by
  unfold comparatorRegret
  induction T with
  | zero => simp
  | succ n ih =>
    have hmin := empiricalMean_minimizes y (n + 1) (by omega) (meanPredict y n)
    have hleader : (∑ t ∈ Finset.range n, (meanPredict y n - y t)^2) =
        ∑ t ∈ Finset.range n, (empiricalMean y n - y t)^2 := by
      by_cases hn : n = 0
      · subst n; simp
      · rw [meanPredict, if_neg hn]
    simp only [Finset.sum_range_succ] at hmin ⊢
    rw [hleader] at hmin
    linarith
'''
write(PUBLIC,prefix+'\n/-- Derived same-FTL loss-gap lower bound; arbitrary real observations, including empty horizon. -/\n'+s['targets'][0]['header']+body+'\nend BanditRL.OnlineLearning\n')
proving_fixed()
write(RUN/'F1-attempt-v1.lean.raw',PUBLIC.read_bytes())
code=gate('F1-focused-v1','lake','build','BanditRLProof.OnlineFTLLimitSemantics',required=False)
write(RUN/'F1-attempt-v1.json',dict(leaf='F1',statement_hash=s['targets'][0]['statement_hash'],
    source_snapshot_sha256=sha(RUN/'F1-attempt-v1.lean.raw'),actual_build_exit=code,
    status='compiled' if code==0 else 'repair',package_accepted=False,chapter_complete=False,goal_complete=False))
gate('F1-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
    '--task',TASK,'--role','lower','--kind','attempt','--status','compiled' if code==0 else 'failed',
    '--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),
    '--statement-hash',s['targets'][0]['statement_hash'],'--attempt-id','F1-v1',
    '--verifier-evidence',(RUN/'F1-focused-v1-exit.json').as_posix(),
    '--notes','Actual focused module build; frozen F1 unchanged; compiler result is not semantic acceptance.',
    '--progress-class','unreviewed','--obligations-before','5','--obligations-after','5')
assert code==0,'Retain failed proof and log; repair same frozen target.'
native('F1-fence-v1','statement-fence','--declaration',s['targets'][0]['name'],'--file',PUBLIC.relative_to(ROOT).as_posix(),
    '--source-assumption','Derived actual strict-past FTL lower bound, all real y and every naturalT including0.',
    '--output',(RUN/'fences/F1-v1.json').relative_to(ROOT).as_posix())
native('F1-safe-v1','safe-verify','--fence',(RUN/'fences/F1-v1.json').relative_to(ROOT).as_posix())
print('F1 actual frozen body focused-compiled; remaining4 and package review/gates required.',flush=True)
