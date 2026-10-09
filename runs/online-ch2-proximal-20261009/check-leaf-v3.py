from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();t=load(CONTRACT/'stabilized-v1.json')['targets'][0]
assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
write(RUN/'repeated-normalization-audit-v2.json',dict(actual_exit=load(RUN/'focused-build-v2.json')['actual_exit'],same_error='scalar H positivity after dsimp; tangent endpoint problem resolved',mathematical_audit='Minimization plus convexity gives fp+hp <= (1-a)fp+a fu+h(q a). H(a) is exactly RHS minus LHS. No missing hypothesis or counterexample.',representation_audit='Remove let-expanding dsimp: explicitly change goal to H expanded with q retained; use order transitivity and explicit ring identity, rather than repeat arithmetic tactic search.',source_or_contract_repair=False,statement_hash=t['statement_hash']))
capture('failed-attempt-native-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed','--attempt-id','PC001-v2','--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',t['statement_hash'],'--verifier-evidence',(RUN/'focused-build-v2.json').relative_to(ROOT).as_posix(),'--error-signature','scalar-let-representation-normalization','--obligations-before','1','--obligations-after','1','--notes','Second actualfocused1; audit actual algebra/let representation before next change. Explicit transitivity and ring equality preserve frozen target.')
write(RUN/'third-body-v3.raw',PUBLIC.read_bytes())
code,out=capture('focused-build-v3','lake','build','BanditRLProof.OnlineProximalComparison',required=False)
write(RUN/'focused-build-inspected-v3.json',dict(actual_exit=code,compiled=code==0 and 'Build completed successfully' in out,body_sha256=sha(PUBLIC),statement_hash=t['statement_hash'],no_source_container_closure=True,whole_Goal_status='ACTIVE'))
print(out[-9000:]);fixed()
