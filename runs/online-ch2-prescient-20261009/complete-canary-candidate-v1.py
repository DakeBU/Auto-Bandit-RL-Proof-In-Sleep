from common import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
fixed();test=ROOT/'Tests/OnlinePrescientLinearCanary.lean'
targets=load(CONTRACT/'canary-stabilized-v1.json')['targets']
for t in targets:assert statement_hash(lean_declaration_header(test,t['declaration']))==t['statement_hash']
assert sha(PUBLIC)=='a7098ef90e812a20616963756f203609758ccc9701d6a30bfe0152cefe3849bc'
b=load(RUN/'canaries-focused-build-v3.json');out=base64.b64decode(b['stdout_base64']).decode('utf8')
assert b['actual_exit']==0 and 'Build completed successfully' in out and 'error:' not in out
assert 'warning: Tests/OnlinePrescientLinearCanary.lean' not in out
write(RUN/'complete-canary-body-v1.raw',test.read_bytes())
context='''import Tests.OnlinePrescientLinearCanary
noncomputable section
open Set Finset
open scoped InnerProductSpace
open BanditRL.OnlinePrescientLinear Tests.OnlinePrescientLinear
namespace Audit.PrescientCanary
'''
for i,t in enumerate(targets,1):
    header=t['exact_proposed_header'].replace('theorem '+t['declaration'].split('.')[-1],'def publicCanaryValue%d'%i,1)
    context+=header+' :=\n  '+t['declaration']+'\n\n#print axioms publicCanaryValue%d\n#print axioms '%i+t['declaration']+'\n#check @'+t['declaration']+'\n\n'
context+='end Audit.PrescientCanary\n';write(RUN/'CompleteCanaryProbe.lean',context)
_,out=capture('complete-canaries-public-values-axioms-v1','lake','env','lean',RUN/'CompleteCanaryProbe.lean')
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",out,re.S);assert len(found)==10
for n,ax in found:assert set(re.findall(r'[A-Za-z_.]+',ax))=={'propext','Classical.choice','Quot.sound'},(n,ax)
fences=[]
for i,t in enumerate(targets,1):
    f=RUN/'complete-canary-fences-v1'/('%02d.json'%i)
    capture('complete-canary-fence-%02d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',t['declaration'],'--file',test,'--output',f)
    assert load(f)['statement_hash']==t['statement_hash']
    _,safe=capture('complete-canary-safe-%02d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',f,'--lean-file',test,'--lean-file',PUBLIC)
    r=json.loads(safe);assert r['ok'] and r['findings']==[]
    fences.append(dict(declaration=t['declaration'],statement_hash=t['statement_hash'],actual_safe_report=r))
export=(RUN/'export-production-dependencies-v1.lean').read_text(encoding='utf8')
export=export.replace('import BanditRLProof.OnlinePrescientLinear\n','import BanditRLProof.OnlinePrescientLinear\nimport Tests.OnlinePrescientLinearCanary\n',1)
start=export.index('def targets : Array Name := #[');end=export.index('\n\ndef moduleName',start)
names=[t['declaration'] for t in load(CONTRACT/'stabilized-v1.json')['targets']]+[t['declaration'] for t in targets]
names+=['BanditRL.OnlinePrescientLinear.'+n for n in ['advance','iterate','prediction','regret']]+['Tests.OnlinePrescientLinear.'+n for n in ['interval','whole','signals']]+['BanditRL.OnlineGradientDescent.'+n for n in ['project','project_spec','project_eq_of_variational']]+['BanditRL.OnlineGradientDescentSource.gradient_linear']
export=export[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+export[end:]
export=export.replace('Lean.importModules #[{ module := `BanditRLProof.OnlinePrescientLinear }]','Lean.importModules #[{ module := `BanditRLProof.OnlinePrescientLinear }, { module := `Tests.OnlinePrescientLinearCanary }]')
export=export.replace('  for n in targets do\n','''  let mut selected := targets
  let mut i := 0
  while i < selected.size do
    let n := selected[i]!
    i := i + 1
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing proof {n}"
    for dep in deps value do
      if dep.toString.startsWith "_private.Tests.OnlinePrescientLinearCanary." && !selected.contains dep then
        selected := selected.push dep
  for n in selected do
''',1)
export=export.replace('Seven frozen affine prescient producer-chain terminals, four actual recursive definitions and existing projection parents. Selected compiled direct TYPE_VALUE constant presence only; not occurrence counts, transitive graph, full shared registry, seven printed theorems or chapter acceptance.','Seven frozen production terminals, five exact canaries, actual definitions/projection/gradient parents and recursively selected private scalar Test helpers. Direct TYPE_VALUE constant presence only; private helper traversal does not make this the full transitive or shared registry graph. Counts are not printed results or chapter acceptance.')
write(RUN/'export-combined-selected-dependencies-v1.lean',export)
capture('complete-combined-selected-graph-command-v1','lake','env','lean','--run',RUN/'export-combined-selected-dependencies-v1.lean',RUN/'complete-combined-selected-graph-data-v1.json')
graph=load(RUN/'complete-combined-selected-graph-data-v1.json');nodes={n['name']:n for n in graph['nodes']}
p='BanditRL.OnlinePrescientLinear.';t='Tests.OnlinePrescientLinear.'
pairs=load(RUN/'complete-production-inspected-candidate-v1.json')['required_VALUE_pairs']+[[t+'current_and_future_information',p+'prediction_prefix'],[t+'outside_initial_center_and_empty_horizon',p+'regret_sharp_bound'],[t+'constrained_gradient_sign_counterexample','BanditRL.OnlineGradientDescentSource.gradient_linear']]
for a,z in pairs:assert z in nodes[a]['value_dependencies'],(a,z)
private_nodes=[n for n in nodes if n.startswith('_private.Tests.OnlinePrescientLinearCanary.')]
assert len(private_nodes)==6
for name in private_nodes:
    if any(x in name for x in ['interval_project_','whole_project']):assert 'BanditRL.OnlineGradientDescent.project_eq_of_variational' in nodes[name]['value_dependencies']
write(RUN/'complete-canary-inspected-candidate-v1.json',dict(stage='five actual frozen bodies compiled; distinct canary BODY and publication review pending',test_sha256=sha(test),production_sha256=sha(PUBLIC),focused_sha256=sha(RUN/'canaries-focused-build-v3.json'),public_values_axioms_sha256=sha(RUN/'complete-canaries-public-values-axioms-v1.json'),actual_axiom_outputs=[dict(declaration=n,axioms=re.findall(r'[A-Za-z_.]+',ax)) for n,ax in found],fences=fences,selected_graph_sha256=sha(RUN/'complete-combined-selected-graph-data-v1.json'),selected_nodes=len(nodes),coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),private_test_helper_nodes=private_nodes,required_VALUE_pairs=pairs,native_guard_is_compilation=False,source_container_closed=False,package_accepted=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('Five public values, standard-only axioms, exact headers and actual selected producer/helper VALUE calls inspected.')
