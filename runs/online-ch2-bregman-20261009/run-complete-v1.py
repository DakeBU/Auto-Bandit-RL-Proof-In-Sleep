from common import *
fixed()
capture('algebra-leaf-status-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','compiled','--attempt-id','BG001-algebra-v1','--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',load(CONTRACT/'stabilized-v1.json')['targets'][1]['statement_hash'],'--obligations-before','2','--obligations-after','0','--notes','Two frozen algebraic bodies focused-build actual0. Compiled only, not accepted; other three proofs and source/chapter/Goal open.')
capture('remaining-leaf-running-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','running','--attempt-id','BG002-comparison-v1','--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',load(CONTRACT/'stabilized-v1.json')['targets'][3]['statement_hash'],'--obligations-before','3','--obligations-after','3','--notes','Finite dependency-ready nonnegative, gradient conversion and actual proximal comparison; all frozen headers unchanged.')
write(RUN/'production-complete-attempt-v1.lean',PUBLIC.read_bytes())
rc,out=capture('focused-complete-build-v1','lake','build','BanditRLProof.OnlineBregmanProximal',required=False)
print(out[-8000:],flush=True)
fixed()
