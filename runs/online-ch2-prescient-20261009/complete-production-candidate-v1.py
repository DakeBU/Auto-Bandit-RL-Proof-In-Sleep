from common import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
fixed()
c=load(CONTRACT/'stabilized-v1.json'); targets=c['targets']
assert hashlib.sha256(PUBLIC.read_bytes()[:2653]).hexdigest()=='fdbf672c0d72c01890e71199be70966e1c56c7dc0c299254b8b124c851eb9a34'
for t in targets: assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
b=load(RUN/'complete-production-focused-build-v1.json')
out=base64.b64decode(b['stdout_base64']).decode('utf8')
assert b['actual_exit']==0 and 'Build completed successfully' in out and 'error:' not in out
write(RUN/'complete-production-body-v1.raw',PUBLIC.read_bytes())
probe='''import BanditRLProof.OnlinePrescientLinear
noncomputable section
open Set Finset
open scoped InnerProductSpace
open BanditRL.OnlineGradientDescent (Domain)
open BanditRL.OnlinePrescientLinear
namespace Audit.Prescient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
'''
args=['V η hη g x u hu','V η hη g x b','V η g x0 t','V η g g\' x0 t h','V η g b x0 u T','V η hη g x0 u T hu','V η hη g x0 u T hu']
for i,(t,a) in enumerate(zip(targets,args),1):
    header=t['exact_proposed_header'].replace('theorem '+t['declaration'].split('.')[-1],'def publicValue%d'%i,1)
    probe+=header+' :=\n  '+t['declaration']+' '+a+'\n\n#print axioms publicValue%d\n#print axioms '%i+t['declaration']+'\n#check @'+t['declaration']+'\n\n'
probe+='end Audit.Prescient\n'; write(RUN/'CompleteProductionProbe.lean',probe)
_,out=capture('complete-production-public-values-axioms-v1','lake','env','lean',RUN/'CompleteProductionProbe.lean')
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",out,re.S)
assert len(found)==14
for n,ax in found: assert set(re.findall(r'[A-Za-z_.]+',ax))=={'propext','Classical.choice','Quot.sound'},(n,ax)
fences=[]
for i,t in enumerate(targets,1):
    f=RUN/'complete-production-fences-v1'/('%02d.json'%i)
    capture('complete-production-fence-%02d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',t['declaration'],'--file',PUBLIC,'--output',f)
    assert load(f)['statement_hash']==t['statement_hash']
    _,safe=capture('complete-production-safe-%02d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',f,'--lean-file',PUBLIC)
    r=json.loads(safe); assert r['ok'] and r['findings']==[]
    fences.append(dict(declaration=t['declaration'],hash=t['statement_hash'],actual_safe_report=r))
# Reuse the reviewed exporter mechanism, with explicit selected production scope only.
parent=ROOT/'runs/online-ch2-chapter-audit-20261009/export-nonsmooth-dependencies-v1.lean'
export=parent.read_text(encoding='utf8')
export=export.replace('import BanditRLProof.OnlineNonsmoothExamples\nimport Tests.OnlineNonsmoothExamplesCanary','import BanditRLProof.OnlinePrescientLinear')
names=[t['declaration'] for t in targets]+['BanditRL.OnlinePrescientLinear.'+n for n in ['advance','iterate','prediction','regret']]+['BanditRL.OnlineGradientDescent.project','BanditRL.OnlineGradientDescent.project_spec']
start=export.index('def targets : Array Name := #[');end=export.index('\n\ndef moduleName',start)
export=export[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+export[end:]
export=export.replace('Lean.importModules #[{ module := `BanditRLProof.OnlineNonsmoothExamples }, { module := `Tests.OnlineNonsmoothExamplesCanary }]','Lean.importModules #[{ module := `BanditRLProof.OnlinePrescientLinear }]')
export=export.replace('Three exact new nonsmooth production proofs, five complementary canary proofs and actual shared parents. Selected direct TYPE_VALUE constant presence, not occurrence counts, full transitive graph, shared registry, new source theorem count or chapter acceptance.','Seven frozen affine prescient producer-chain terminals, four actual recursive definitions and existing projection parents. Selected compiled direct TYPE_VALUE constant presence only; not occurrence counts, transitive graph, full shared registry, seven printed theorems or chapter acceptance.')
write(RUN/'export-production-dependencies-v1.lean',export)
capture('complete-production-graph-command-v1','lake','env','lean','--run',RUN/'export-production-dependencies-v1.lean',RUN/'complete-production-graph-data-v1.json')
graph=load(RUN/'complete-production-graph-data-v1.json');nodes={n['name']:n for n in graph['nodes']}
p='BanditRL.OnlinePrescientLinear.';q='BanditRL.OnlineGradientDescent.'
pairs=[(p+'advance_sharp_bound',q+'project_spec'),(p+'advance_proximal_minimizer',p+'advance_sharp_bound'),(p+'prediction_mem',q+'project_spec'),(p+'regret_sharp_bound',p+'advance_sharp_bound'),(p+'regret_source_bound',p+'regret_sharp_bound'),(p+'advance',q+'project'),(p+'iterate',p+'advance'),(p+'prediction',p+'iterate'),(p+'regret',p+'prediction')]
for a,z in pairs: assert z in nodes[a]['value_dependencies'],(a,z)
write(RUN/'complete-production-inspected-candidate-v1.json',dict(stage='actual7frozen bodies compiled; distinct complete BODY review pending',production_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'complete-production-body-v1.raw'),focused_sha256=sha(RUN/'complete-production-focused-build-v1.json'),public_values_axioms_sha256=sha(RUN/'complete-production-public-values-axioms-v1.json'),actual_axiom_outputs=[dict(declaration=n,axioms=re.findall(r'[A-Za-z_.]+',ax)) for n,ax in found],fences=fences,selected_graph_sha256=sha(RUN/'complete-production-graph-data-v1.json'),selected_nodes=len(nodes),coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),required_VALUE_pairs=pairs,native_guard_is_compilation=False,source_container_closed=False,package_accepted=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('Actual seven public values, standard-only axioms, frozen guards and selected compiled dependencies inspected.')
