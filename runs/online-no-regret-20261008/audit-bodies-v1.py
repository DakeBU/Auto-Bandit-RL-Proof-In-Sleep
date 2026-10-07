from common_reviewed_v1 import *
import re
reviewed_fixed()
for label in ['all-nine-focused-build-v2','public-canary-build-v2']:
 assert load(RUN/(label+'-exit.json'))['exit_code']==0
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header
PRE='BanditRL.OnlineLearning.';TEST='NoRegretSemanticsProbe.'
targets=load(CONTRACT/'targets-v1.json')['targets']
actual=[]
for row in targets:
 h=lean_declaration_header(PUBLIC,row['name'].rsplit('.',1)[1])
 assert h==row['header'] and hashlib.sha256(h.encode()).hexdigest()==row['header_sha256'],row['name']
 actual.append(dict(name=row['name'],path=PUBLIC.as_posix(),header=h))
for n in re.findall(r'(?m)^theorem (\w+)\b',CANARY.read_text(encoding='utf8')):
 actual.append(dict(name=TEST+n,path=CANARY.as_posix(),header=lean_declaration_header(CANARY,n)))
assert len(actual)==24
write(RUN/'actual-public-canary-headers-v1.json',actual)
write(RUN/'public-candidate-v2.lean.raw',PUBLIC.read_bytes())
write(RUN/'canary-candidate-v2.lean.raw',CANARY.read_bytes())
reuse=load(CONTRACT/'targets-v1.json')['existing_reuse']
context=[PRE+'LimitNoRegret',PRE+'NoRegretCounterexample.potential',PRE+'NoRegretCounterexample.loss',PRE+'comparatorRegret',PRE+'NoRegret',PRE+'meanPredict']
names=[x['name'] for x in actual]+reuse+context+[TEST+'linearLoss']
assert len(names)==len(set(names))==34
write(RUN/'leaves/all-axioms-v1.lean','import Tests.OnlineNoRegretSemanticsCanary\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names))
gate('all-axioms-v1','lake','env','lean',RUN/'leaves/all-axioms-v1.lean')
log=(RUN/'all-axioms-v1.log').read_text(encoding='utf8');assert 'sorryAx' not in log
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(matched)==34
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write(RUN/'axiom-bindings-v1.json',dict(names=names,axioms=axioms,count=34,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY)))
# Remove only the proposed inlined context: this probe imports the ACTUAL compiled module.
s=(RUN/'draft-proposition-identities-v4.lean').read_text(encoding='utf8')
context_text='\n'.join(x for x in (CONTRACT/'public-context-v1.lean').read_text(encoding='utf8').splitlines() if not x.startswith('import ')).strip()
assert s.count(context_text)==1
s=s.replace(context_text,'',1)
s='import Tests.OnlineNoRegretSemanticsCanary\n'+s
s+='\nnamespace ActualTypeVerification\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
for i,n in enumerate([x['name'] for x in targets]+reuse,1):
 suffix='.{v}' if i in [1,2,3,11,12] else ''
 s+=f'example : DraftTypeVerification.A{i:03}{suffix} = propositionOf (@{n}{suffix}) := by rfl\n'
for a,b,suffix in [('r',PRE+'comparatorRegret','.{v}'),('upper',PRE+'NoRegret','.{v}'),('limit',PRE+'LimitNoRegret','.{v}'),('h',PRE+'NoRegretCounterexample.potential',''),('f',PRE+'NoRegretCounterexample.loss',''),('q',PRE+'meanPredict','')]:
 s+=f'example : @NeutralPacket.{a}{suffix} = @{b}{suffix} := by rfl\n'
s+='open NoRegretSemanticsProbe\n'
for i,row in enumerate(actual[9:],1):
 h=row['header'];short=row['name'].rsplit('.',1)[1]
 rest=h.removeprefix('theorem '+short).strip()
 bind,result=rest.split(':',1) if rest.startswith(':') else (None,None)
 if rest.startswith(':'):p=result.strip()
 else:
  # All canary binders here are explicit and their terminal separator is colon-newline.
  bind,result=rest.split(':\n',1);p='∀ '+bind.strip()+',\n'+result.strip()
 s+=f'\ndef C{i:03} : Prop := {p}\nexample : C{i:03} = propositionOf (@{row["name"]}) := by rfl\n'
s+='\nnoncomputable def linearFixture (_ : ℕ) (u : ℝ) : ℝ := u\nexample : linearFixture = NoRegretSemanticsProbe.linearLoss := by rfl\nend ActualTypeVerification\n'
write(RUN/'leaves/all-exact-types-v1.lean',s)
gate('all-exact-types-v1','lake','env','lean',RUN/'leaves/all-exact-types-v1.lean')
template=Path('runs/online-regret-domains-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineLearningRegretDomainsCanary','Tests.OnlineNoRegretSemanticsCanary')
template=template.replace('Existing2shared Regret proofs/2definitions plus8named validation proofs/8fixturedefinitions. Selected20compiled nodes with direct type/VALUE references; zero new production nodes; not the full shared registry or source inventory.','Nine new public reconciliation proofs/three reused proofs/six scoped context definitions, fifteen named canary proofs/one test definition. Selected34 compiled nodes; actual direct TYPE and VALUE constant occurrences, not a full registry or teaching/source inventory.')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==34
assert sum(x['kind']=='theorem' for x in graph['nodes'])==27
assert sum(x['kind']=='definition' for x in graph['nodes'])==7
assert all(x['has_value'] for x in graph['nodes'])
counter=PRE+'NoRegretCounterexample.'
required=[
 (PRE+'noRegret_limit_nonpos','le_of_tendsto'),
 (PRE+'limitNoRegret_implies_noRegret','tendsto_order'),
 (PRE+'limitNoRegret_iff_noRegret_of_converges',PRE+'noRegret_limit_nonpos'),
 (PRE+'limitNoRegret_iff_noRegret_of_converges',PRE+'limitNoRegret_implies_noRegret'),
 (counter+'regret_eq','Finset.sum_range_succ'),
 (counter+'noRegret',counter+'regret_eq'),
 (counter+'normalized_even',counter+'regret_eq'),
 (counter+'normalized_odd',counter+'regret_eq'),
 (counter+'no_limit',counter+'normalized_even'),
 (counter+'no_limit',counter+'normalized_odd'),
 (counter+'no_limit','tendsto_nhds_unique'),
 (counter+'no_limit','Filter.tendsto_atTop_mono'),
 (counter+'strict_separation',counter+'noRegret'),
 (counter+'strict_separation',counter+'no_limit'),
 (TEST+'linear_upper',PRE+'limitNoRegret_implies_noRegret'),
 (TEST+'negative_limit_allowed',PRE+'noRegret_limit_nonpos'),
 (TEST+'iff_on_linear',PRE+'limitNoRegret_iff_noRegret_of_converges'),
 (TEST+'actual_mean_upper',PRE+'meanPredict_noRegret'),
 (TEST+'same_process_strict',counter+'strict_separation')]
edges={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in required:assert pair in edges,pair
write(RUN/'required-value-pairs-v1.json',dict(required_pairs=required,status='Actual compiled VALUE occurrences, not a teaching DAG'))
fences=[]
for row in actual:
 short=row['name'].rsplit('.',1)[1];path=Path(row['path']);label=('public-' if path==PUBLIC else 'canary-')+short
 fence=RUN/'full-header-fences-v1'/(label+'.json')
 native('full-fence-'+label+'-v1','statement-fence','--declaration',row['name'],'--file',path,'--source-assumption',row['header'],'--output',fence)
 native('full-safe-'+label+'-v1','safe-verify','--fence',fence,'--lean-file',path)
 assert load(fence)['statement']==row['header']
 fences.append(dict(name=row['name'],path=fence.as_posix(),sha256=sha(fence),statement_hash=load(fence)['statement_hash']))
write(RUN/'full-fence-bindings-v1.json',fences)
native('actual-public-lookup-v1','list-lean-decls','--statement',PRE+'NoRegret')
native('actual-bridge-lookup-v1','list-lean-decls','--statement','Regret_')
native('actual-canary-lookup-v1','list-lean-decls','--include-tests','--statement',TEST)
write(RUN/'body-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),frozen_targets=9,new_public_proofs=9,new_public_definitions=3,reused_public_proofs=3,named_canary_proofs=15,test_definitions=1,named_kernel_checks=34,neutral_closed_proposition_identities=12,actual_canary_proposition_identities=15,whole_definition_identities=7,axioms=axioms,selected_compiled_nodes=34,proof_nodes=27,definition_nodes=7,direct_references=len(graph['edges']),required_value_pairs=required,full_native_proof_fences=24,safe_verify_scope='Header hash, source substring and forbidden token scan only; actual Lean compilation is independent focused/kernel/Prop-identity evidence.',nine_derived_reconciliation_targets_closed=True,BODY_review='pending',combined_reader_FINAL_native_PR='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-all-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','NO-REGRET-ALL-V1','--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--target-fingerprint',sha(CONTRACT/'targets-v1.json'),'--progress-class','terminal','--obligations-before','9','--obligations-after','0','--new-declaration',counter+'strict_separation','--notes','Only nine immutable reconciliation terminals closed. Actual telescoping affine stream and positive cofinal even/odd normalized regret, generic finite-limit bridges. Nine are derived support, not source numbered theorems. All package BODY/integrated/source-reader/FINAL/delivery and whole-book obligations remain pending.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,body_bindings=(RUN/'body-bindings-v1.json').as_posix(),contract_version=1,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
reviewed_fixed();print('34 actual kernel nodes, 12 neutral/15 actual canary Prop and 7 whole definition equalities; candidate BODY review pending.')
