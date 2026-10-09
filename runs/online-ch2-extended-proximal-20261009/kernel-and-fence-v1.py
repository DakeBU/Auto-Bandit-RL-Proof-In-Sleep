from common import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();d=load(CONTRACT/'stabilized-v1.json')
build=load(RUN/'focused-complete-build-v1.json');out=base64.b64decode(build['stdout_base64']).decode('utf8')
assert build['actual_exit']==0 and 'Build completed successfully (3297 jobs).' in out
for t in d['targets']:assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash'],t['declaration']
context='variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n'
probe='import BanditRLProof.OnlineBregmanExtended\nopen Set BanditRL.OnlineBregman\nnamespace OnlineBregmanExtendedAudit\n'
calls=['f V hV hp hs','f V ψ η x p hp hfin','f V hV hf hs ψ η hη x p hp hdx hdp hmin']
for i,(t,call) in enumerate(zip(d['targets'],calls)):
    short=t['declaration'].rsplit('.',1)[1]
    probe+='section\n'+context+('variable [CompleteSpace E]\n' if i else '')
    probe+=t['exact_proposed_header'].replace('theorem '+short,'theorem public_value_'+str(i))+' :=\n  '+t['declaration']+' '+call+'\n'
    probe+='#check '+t['declaration']+'\n#print '+t['declaration']+'\n#print axioms '+t['declaration']+'\n#print axioms public_value_'+str(i)+'\nend\n'
probe+='end OnlineBregmanExtendedAudit\n'
write(RUN/'PublicAPIProbe.lean',probe)
code,out=capture('public-VALUE-kernel-v1','lake','env','lean',RUN/'PublicAPIProbe.lean')
axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',out)
assert len(axioms)==6 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for a in axioms)
for cmd in ['statement-fence','safe-verify']:capture(cmd+'-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py',cmd,'--help')
for i,t in enumerate(d['targets']):
    capture('public-lookup-'+str(i)+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls',t['declaration'].rsplit('.',1)[1],'--statement')
    fence=(CONTRACT/('statement-fence-'+str(i)+'-v1.json')).relative_to(ROOT).as_posix()
    capture('statement-fence-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',t['declaration'],'--file',PUBLIC.relative_to(ROOT).as_posix(),'--output',fence)
    capture('safe-verify-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',fence,'--lean-file',PUBLIC.relative_to(ROOT).as_posix())
    assert load(ROOT/fence)['statement_hash']==t['statement_hash']
write(RUN/'kernel-and-fence-inspected-v1.json',dict(actual_kernel_exit=code,production_sha256=sha(PUBLIC),public_generic_VALUE_count=3,axiom_outputs=axioms,standard_only=True,all_three_statement_hashes_unchanged=True,actual_cached_inclusive_build_jobs=3297,explicit_warning='Only existing parent warnings replayed; no new production warnings or suppression. Existing minOn API completeness explicitly retained.',nondegenerate_canary_pending=True,BODY_review_pending=True,combined_gates_pending=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('terminal-compiled-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','compiled','--attempt-id','EP002-extended-terminal-v1','--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',d['targets'][2]['statement_hash'],'--obligations-before','1','--obligations-after','0','--verifier-evidence',RUN/'focused-complete-build-v1.json','--notes','Actualfocused3297jobs0 and3fullgenericpublicVALUEs/6standard-onlyaxioms/3frozenheaders-nativefences-safechecks. Onlycompiledproduction, canaries/BODY/combined/publicationFINALpending. Fullsource/causal/attainment/interiority/telescopes/all8forwards/GoalOPEN.')
event('production-candidate-native-v1','candidate',dict(scope='Only3compiledsourcebridgebodies; notpackageaccepted',evidence_sha256=sha(RUN/'kernel-and-fence-inspected-v1.json'),canaries_PENDING=True,BODY_PENDING=True,combined_PENDING=True,source_container_closed=False,chapter_complete=False,goal_complete=False))
fixed();print('Actual3publicVALUEs/6standard-onlyaxioms/3frozenheaderfences inspected; canaries/BODY/combined stillpending.')
