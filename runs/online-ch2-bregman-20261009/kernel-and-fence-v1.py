from common import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed()
d=load(CONTRACT/'stabilized-v1.json')
text=PUBLIC.read_text(encoding='utf8')
assert d['definition']['exact_definition'] in text
assert hashlib.sha256(d['definition']['exact_definition'].encode('utf8')).hexdigest()==d['definition']['definition_term_sha256']
for t in d['targets']:
    assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash'],t['declaration']
normed='variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]\n'
inner='variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]\n'
probe='import BanditRLProof.OnlineBregmanProximal\nopen Set BanditRL.OnlineBregman\nnamespace OnlineBregmanAudit\n'
calls=['ψ x','ψ x y z','X ψ hψ x y hx hy hd','V f ψ η hη x p hp hf hdx hdp hmin','ψ x y hd']
for i,(t,call) in enumerate(zip(d['targets'],calls)):
    short=t['declaration'].rsplit('.',1)[1]
    probe+='section\n'+(inner if i==4 else normed)
    probe+=t['exact_proposed_header'].replace('theorem '+short,'theorem public_value_'+str(i))+' :=\n  '+t['declaration']+' '+call+'\n'
    probe+='#check '+t['declaration']+'\n#print '+t['declaration']+'\n#print axioms '+t['declaration']+'\n#print axioms public_value_'+str(i)+'\nend\n'
probe+='end OnlineBregmanAudit\n'
write(RUN/'PublicAPIProbe.lean',probe)
code,out=capture('public-VALUE-kernel-v1','lake','env','lean',RUN/'PublicAPIProbe.lean')
axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',out)
assert len(axioms)==10 and 'sorryAx' not in out,(len(axioms),out[-1000:])
assert all(set(x.strip() for x in a.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for a in axioms)
for i,t in enumerate(d['targets']):
    capture('public-lookup-'+str(i)+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls',t['declaration'].rsplit('.',1)[1],'--statement')
    capture('statement-fence-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',t['declaration'],'--file',PUBLIC.relative_to(ROOT).as_posix(),'--output',(CONTRACT/('statement-fence-'+str(i)+'-v1.json')).relative_to(ROOT).as_posix())
    capture('safe-verify-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',(CONTRACT/('statement-fence-'+str(i)+'-v1.json')).relative_to(ROOT).as_posix(),'--lean-file',PUBLIC.relative_to(ROOT).as_posix())
    assert load(CONTRACT/('statement-fence-'+str(i)+'-v1.json'))['statement_hash']==t['statement_hash']
write(RUN/'kernel-and-fence-inspected-v1.json',dict(actual_kernel_exit=code,production_sha256=sha(PUBLIC),public_generic_VALUE_count=5,axiom_outputs=axioms,standard_only=True,all_five_statement_hashes_unchanged=True,canonical_definition_unchanged=True,focused_build_compiled='Build completed successfully (2391 jobs).' in base64.b64decode(load(RUN/'focused-complete-build-v2.json')['stdout_base64']).decode('utf8'),explicit_warning='unused hdx retained in the frozen source-faithful statement; proof clears it because the fixed actual dual map is already linear',nondegenerate_canary_pending=True,body_review_pending=True,combined_gates_pending=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Five exact full generic public VALUE probes, ten standard-only axiom outputs, native fences and safe checks inspected.')
