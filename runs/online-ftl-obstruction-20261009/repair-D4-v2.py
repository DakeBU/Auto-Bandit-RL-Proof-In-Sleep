from common_proving_v1 import *
s=proving_fixed();t=s['targets'][3]
assert load(RUN/'D4-attempt-v1.json')['actual_build_exit']==1
before=PUBLIC.read_bytes(); failed=(RUN/'D4-attempt-v1.lean.raw').read_bytes()
assert before==failed
old='(tendsto_const_nhds.sub dyadic_empiricalMean_subsequences.'
new='((tendsto_const_nhds (x := (0 : ℝ))).sub dyadic_empiricalMean_subsequences.'
text=before.decode('utf8');assert text.count(old)==2
PUBLIC.write_bytes(text.replace(old,new).encode('utf8'))
proving_fixed();write(RUN/'D4-attempt-v2.lean.raw',PUBLIC.read_bytes())
code=gate('D4-focused-v2','lake','build','BanditRLProof.OnlineFTLOscillation',required=False)
write(RUN/'D4-attempt-v2.json',dict(leaf='D4',statement_hash=t['statement_hash'],
    actual_build_exit=code,status='compiled' if code==0 else 'repair',
    failed_attempt_sha256=sha(RUN/'D4-attempt-v1.lean.raw'),source_sha256=sha(PUBLIC),
    repair='Explicit constant zero for Lean inference; frozen terminal and earlier proof bytes unchanged.',
    package_accepted=False,chapter_complete=False,goal_complete=False))
gate('D4-trial-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
    '--task',TASK,'--role','lower','--kind','attempt','--status','compiled' if code==0 else 'failed',
    '--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',t['statement_hash'],
    '--attempt-id','D4-v2','--verifier-evidence',RUN/'D4-focused-v2-exit.json',
    '--progress-class','unreviewed','--obligations-before','4','--obligations-after','4',
    '--notes','Retained v1 failed implicit-zero inference; body-only explicit zero repair. Semantic and full gates pending.')
assert code==0
native('D4-fence-v2','statement-fence','--declaration',t['name'],'--file',PUBLIC.relative_to(ROOT),
    '--output',RUN/'fences/D4-v2.json')
native('D4-safe-v2','safe-verify','--fence',RUN/'fences/D4-v2.json')
