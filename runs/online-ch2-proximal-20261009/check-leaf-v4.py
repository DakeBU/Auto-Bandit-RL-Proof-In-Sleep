from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();t=load(CONTRACT/'stabilized-v1.json')['targets'][0]
assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
write(RUN/'third-failure-order-API-audit-v1.json',dict(actual_exit=load(RUN/'focused-build-v3.json')['actual_exit'],kind='Pinned additive monotonicity helper orientation differs from recalled name.',actual_typed_API='add_le_add_left bc a : b+a<=c+a; add_le_add_right bc a : a+b<=a+c',probe_sha256=sha(RUN/'order-API-v1.json'),probe_exit=1,probe_boundary='Three target generic signatures printed. Last3 optional real-specialized checks failed because Convex.Function alone does not import real notation. No target body was inferred from probe exit.',repair='Use actual typed add_le_add_left for f(q a)+h(q a); no mathematical/hypothesis/header change.',statement_hash=t['statement_hash']))
capture('failed-attempt-native-v3',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed','--attempt-id','PC001-v3','--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',t['statement_hash'],'--verifier-evidence',(RUN/'focused-build-v3.json').relative_to(ROOT).as_posix(),'--error-signature','pinned-additive-monotonicity-orientation','--obligations-before','1','--obligations-after','1','--notes','Actualfocused1; exact generic add_le_add signatures retrieved before repair. No silent target weakening.')
write(RUN/'fourth-body-v4.raw',PUBLIC.read_bytes())
code,out=capture('focused-build-v4','lake','build','BanditRLProof.OnlineProximalComparison',required=False)
write(RUN/'focused-build-inspected-v4.json',dict(actual_exit=code,compiled=code==0 and 'Build completed successfully' in out,body_sha256=sha(PUBLIC),statement_hash=t['statement_hash'],no_source_container_closure=True,whole_Goal_status='ACTIVE'))
print(out[-9000:]);fixed()
