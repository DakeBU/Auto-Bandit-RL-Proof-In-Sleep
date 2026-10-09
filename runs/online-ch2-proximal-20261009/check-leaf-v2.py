from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();t=load(CONTRACT/'stabilized-v1.json')['targets'][0]
assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
write(RUN/'first-failure-classification-v1.json',dict(kind='local polynomial normalization and implicit endpoint elaboration',actual_focused_exit=load(RUN/'focused-build-v1.json')['actual_exit'],source_or_contract_repair=False,statement_hash_unchanged=True,repair='Use nonlinear polynomial normalization for convex combination algebra; annotate exact segment0to1 before tangent API. No new assumptions or declarations.'))
event('repair-proof-v1','repair',dict(kind='implementation-api-and-normalization',fixed_statement_hash=t['statement_hash'],failure_sha256=sha(RUN/'focused-build-v1.json'),source_or_contract_change=False))
capture('failed-attempt-native-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed','--attempt-id','PC001-v1','--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',t['statement_hash'],'--verifier-evidence',(RUN/'focused-build-v1.json').relative_to(ROOT).as_posix(),'--error-signature','polynomial-linear-normalization;implicit-segment-endpoints','--obligations-before','1','--obligations-after','1','--notes','Actual first focused exit1; local implementation only, frozen target unchanged.')
write(RUN/'second-body-v2.raw',PUBLIC.read_bytes())
code,out=capture('focused-build-v2','lake','build','BanditRLProof.OnlineProximalComparison',required=False)
write(RUN/'focused-build-inspected-v2.json',dict(actual_exit=code,compiled=code==0 and 'Build completed successfully' in out,body_sha256=sha(PUBLIC),statement_hash=t['statement_hash'],no_source_container_closure=True,whole_Goal_status='ACTIVE'))
print(out[-9000:]);fixed()
