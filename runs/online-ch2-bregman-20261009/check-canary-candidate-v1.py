from common import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed()
p=ROOT/'Tests/OnlineBregmanProximalCanary.lean'
d=load(CONTRACT/'canary-stabilized-v1.json')
build=load(RUN/'focused-canary-build-v3.json')
out=base64.b64decode(build['stdout_base64']).decode('utf8')
assert build['actual_exit']==0 and 'Build completed successfully' in out
assert sha(PUBLIC)==d['production_sha256']
probe='import Tests.OnlineBregmanProximalCanary\nopen Set BanditRL.OnlineBregman\nnamespace OnlineBregmanCanaryAudit\n'
for i,t in enumerate(d['targets']):
    assert statement_hash(lean_declaration_header(p,t['declaration']))==t['statement_hash']
    assert hashlib.sha256(t['exact_proposed_header'].encode('utf8')).hexdigest()==t['header_raw_sha256']
    short=t['declaration'].rsplit('.',1)[1]
    probe+=t['exact_proposed_header'].replace('theorem '+short,'theorem public_value_'+str(i))+' :=\n  '+t['declaration']+'\n'
    probe+='#check '+t['declaration']+'\n#print axioms '+t['declaration']+'\n#print axioms public_value_'+str(i)+'\n'
probe+='end OnlineBregmanCanaryAudit\n'
write(RUN/'CanaryPublicValues.lean',probe)
rc,out=capture('canary-public-VALUE-kernel-v1','lake','env','lean',RUN/'CanaryPublicValues.lean')
axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',out)
assert len(axioms)==4 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for a in axioms)
for i,t in enumerate(d['targets']):
    fence=CONTRACT/('canary-fence-'+str(i)+'-v1.json')
    capture('canary-fence-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',t['declaration'],'--file',p.relative_to(ROOT).as_posix(),'--output',fence.relative_to(ROOT).as_posix())
    capture('canary-safe-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',fence.relative_to(ROOT).as_posix(),'--lean-file',p.relative_to(ROOT).as_posix())
    assert load(fence)['statement_hash']==t['statement_hash']
old=(ROOT/'runs/online-ch2-proximal-20261009/audit-numeric-tail-v1.lean').read_text(encoding='utf8')
old=old.replace('Tests.OnlineProximalComparisonCanary','Tests.OnlineBregmanProximalCanary').replace('BanditRL.OnlineProximalCanary.nonsmooth_shifted_quadratic','BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth').replace('BanditRL.OnlineProximalCanary.nonconvex_regularizer','BanditRL.OnlineBregmanCanary.boundary_outside_initial').replace('BanditRL.OnlineProximal.convex_minimizer_comparison','BanditRL.OnlineBregman.proximal_one_step')
write(RUN/'audit-numeric-tail-v1.lean',old)
capture('numeric-tail-command-v1','lake','env','lean','--run',RUN/'audit-numeric-tail-v1.lean',RUN/'numeric-tail-data-v1.json')
tails=load(RUN/'numeric-tail-data-v1.json')
assert len(tails['rows'])==2 and all(t['public_helper_in_selected_tail'] for t in tails['rows'])
old=(RUN/'export-production-dependencies-v1.lean').read_text(encoding='utf8')
old=old.replace('import BanditRLProof.OnlineBregmanProximal\n','import BanditRLProof.OnlineBregmanProximal\nimport Tests.OnlineBregmanProximalCanary\n',1)
old=old.replace('`BanditRL.OnlineBregman.divergence_eq_gradient]','`BanditRL.OnlineBregman.divergence_eq_gradient,\n'+',\n'.join('`'+t['declaration'] for t in d['targets'])+']')
old=old.replace('#[{ module := `BanditRLProof.OnlineBregmanProximal }]','#[{ module := `BanditRLProof.OnlineBregmanProximal }, { module := `Tests.OnlineBregmanProximalCanary }]')
old=old.replace('_private.BanditRLProof.OnlineBregmanProximal.','_private.Tests.OnlineBregmanProximalCanary.')
old=old.replace('Five frozen Bregman helper proofs and one complete canonical definition, no Test nodes yet.','Five frozen Bregman helper proofs, one complete canonical definition and two public canary conjunctions.')
write(RUN/'export-selected-dependencies-v1.lean',old)
capture('selected-dependency-command-v1','lake','env','lean','--run',RUN/'export-selected-dependencies-v1.lean',RUN/'selected-dependency-data-v1.json')
graph=load(RUN/'selected-dependency-data-v1.json');nodes={n['name']:n for n in graph['nodes']}
pairs=load(RUN/'production-dependency-inspected-v1.json')['required_actual_VALUE_pairs']
pairs += [[t['declaration'],'BanditRL.OnlineBregman.'+n] for t in d['targets'] for n in ['proximal_one_step','divergence_eq_gradient']]
for a,b in pairs:assert b in nodes[a]['value_dependencies'],(a,b)
write(RUN/'complete-candidate-inspected-v1.json',dict(production_sha256=sha(PUBLIC),test_sha256=sha(p),actual_focused_canary_exit=build['actual_exit'],actual_cached_inclusive_jobs=list(map(int,re.findall(r'Build completed successfully \((\d+) jobs\)',base64.b64decode(build['stdout_base64']).decode('utf8')))),seven_frozen_headers_unchanged=True,complete_definition_unchanged=True,actual_canary_public_VALUEs=2,standard_only=True,actual_canary_axiom_outputs=axioms,selected_nodes=len(nodes),selected_graph_sha256=sha(RUN/'selected-dependency-data-v1.json'),coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),required_actual_VALUE_pairs=pairs,numeric_tail_sha256=sha(RUN/'numeric-tail-data-v1.json'),both_selected_numeric_tails_retain_public_helper=True,nonnegative_concrete_canary_VALUE_use=False,nonnegative_generic_public_VALUE=True,source_container_closed=False,package_accepted=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
event('candidate-native-v1','candidate',dict(production_sha256=sha(PUBLIC),test_sha256=sha(p),evidence_sha256=sha(RUN/'complete-candidate-inspected-v1.json'),scope='Five proofs+one definition, two full public canary conjunctions, two individually selected numeric tails, actual compiled VALUE parents; canary BODY/publication/combined/site/FINAL acceptance pending',source_container_closed=False,chapter_complete=False,goal_complete=False))
fixed()
print('Two actual public canary values/four axioms/two numeric-tail VALUEs and eight required parent pairs inspected; candidate only.')
