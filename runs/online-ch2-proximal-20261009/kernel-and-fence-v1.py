from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();t=load(CONTRACT/'stabilized-v1.json')['targets'][0]
assert sha(PUBLIC)==load(RUN/'focused-build-inspected-v4.json')['body_sha256']
assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
capture('public-lookup-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','convex_minimizer_comparison','--statement')
code,out=capture('public-VALUE-kernel-v1','lake','env','lean',RUN/'PublicAPIProbe.lean')
assert 'sorryAx' not in out and 'depends on axioms' in out
import re
axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',out)
assert len(axioms)==2
assert all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for a in axioms)
capture('statement-fence-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',t['declaration'],'--file',PUBLIC.relative_to(ROOT).as_posix(),'--source-assumption','hp : p ∈ V','--source-assumption','hf : ConvexOn ℝ V f','--source-assumption','hmin : IsMinOn (fun z => f z + h z) V p','--source-assumption','hd : HasFDerivAt h h\' p','--output',(CONTRACT/'statement-fence-v1.json').relative_to(ROOT).as_posix())
capture('safe-verify-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',(CONTRACT/'statement-fence-v1.json').relative_to(ROOT).as_posix(),'--lean-file',PUBLIC.relative_to(ROOT).as_posix())
assert load(CONTRACT/'statement-fence-v1.json')['statement_hash']==t['statement_hash']
write(RUN/'kernel-and-fence-inspected-v1.json',dict(actual_kernel_exit=code,production_sha256=sha(PUBLIC),public_generic_VALUE=True,axiom_outputs=axioms,standard_only=True,statement_hash=t['statement_hash'],focused_build_compiled=True,nondegenerate_canary_pending=True,body_review_pending=True,combined_gates_pending=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('Public full VALUE kernel/standard axioms/frozen native fence actual0; canary and BODY review pending.')
