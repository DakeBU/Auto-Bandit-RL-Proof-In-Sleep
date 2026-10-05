"""Verify distinct contract bindings before actual retained-body verification."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-CONVEX-MIGRATION-20261005'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    p=run/n;p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
r=load(run/'source-contract-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer'
assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_repairs',[]))
assert sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
inventory=load(run/'contract-source-inputs-v1.json')
for row in inventory['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
target_verdicts={n.rsplit('.',1)[-1]:v for n,v in r['target_verdicts'].items()}
assert set(target_verdicts)==set(freeze['headers'])
assert all(v in ['accepted','accepted-with-explicit-delta'] for v in target_verdicts.values())
for p,h in dict(freeze['modules'],**freeze['canaries']).items():assert sha(p)==h,p
for group,names in freeze['groups'].items():
    for n in names:assert hashlib.sha256(lean_declaration_header(Path('BanditRLProof')/(group+'.lean'),n).encode()).hexdigest()==freeze['headers'][n],n
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
assert ready['scope_nodes']==27 and len(ready['required_actual_value_pairs'])==13
write('contract-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(reviewed),fixed_input_rows=len(inventory['rows']),
    distinct_actor=r['actor']['task'],report_sha256=r['report_sha256'],verdict=r['verdict'],frozen_headers=freeze['headers'],
    semantic_slots_per_target=7,future_reader_corrections=r.get('required_reader_corrections',[]),body_package_accepted=False))
for event in ['stabilized','proving']:
    gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',
        json.dumps(dict(run_id=run.name,contract_version=1,source_contract_receipt=str(run/'source-contract-receipt-v1.json'),frozen_headers=freeze['headers'],
            definitions=5,retained_proofs=22,new_proofs=0,route='single lower reuse of actual retained proof bodies',first_ready_leaf='definition_2_2',
            terminals=load(run/'proof-obligations-v1.json')['terminals'],allowed_edit_scope=load(run/'proof-obligations-v1.json')['edit_scope'],
            body_package_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json')
for row in ob['required']:row['state']='source-stabilized-retained-body-fresh-verification-pending'
ob.update(stage='proving',source_contract_verdict=r['verdict'],new_proofs=0,dependency_readiness=str(run/'ready-dependencies-v1.json'))
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md',
    'Four unchanged module bodies inspected. Definition2.2 uses the positive-weight Convex equivalence. Domain convexity lifts endpoints to finite REAL heights even at bottom, takes their convex epigraph combination and bounds below top. '
    'Indicator domain identity is pointwise membership; its epigraph is V times nonnegative real heights, giving both directions of the convexity iff. '
    'The toReal epigraph bridge proves finite-value conversions with noBottom explicitly, and ConvexOn/epigraph iff supports the characterization. Thm2.4 uses hdom to show the combination remains finite, not an implicit no-infinity conversion. '
    'Indicator addition forms epigraph intersection under noBottom and convex V. Real coercion iff reduces Examples2.5/2.6 to an inner-product affine identity and actual pinned norm convexity. '
    'Affine closure is product affine preimage preserving real heights; supremum closure is arbitrary epigraph intersection; real monotone composition chains inner convexity, global monotonicity and outer convexity. '
    'upperAdd finite/top laws unfold the explicit operation; finite-height witnesses are casewise proved for all nine infinity/finite combinations. Convex upper sum combines witnessed epigraph points. '
    'Positive scaling is a casewise finite-height order iff; nonnegative scaling splits zero/positive, using EReal zero-product convention and height rescaling. The terminal uses those actual proved scaling and upper-sum results, without assuming the desired closure. '
    '22 retained bodies/five definitions, zero new source theorems or weakened statements. Four existing public canaries include real/nonconstant values, exact height exclusions, bottom/empty domains, shift/constant maps, empty indexed family, monotone norm composition, improper disjoint spikes, ordinary-addition counterexample, zero and positive weights. Fresh elaboration/axioms/safe guards/body review and integrated gates still pending.')
public=['BanditRL.OnlineConvex.'+n for n in list(freeze['headers'])+sum(freeze['definitions'].values(),[])]
canary=[]
for group in freeze['groups']:
    p=Path('Tests')/(group+'Canary.lean');text=p.read_text(encoding='utf-8')
    namespace=re.search(r'(?m)^namespace\s+(\S+)',text).group(1)
    for n in re.findall(r'(?m)^(?:theorem|lemma|def)\s+(\S+)',text):canary.append(namespace+'.'+n)
names=public+canary;assert len(names)==len(set(names))==53
probe='import BanditRLProof\n'+''.join('import Tests.'+group+'Canary\n' for group in freeze['groups'])+'\n'
for n in names:probe+='#check @'+n+'\n#print axioms '+n+'\n'
write('leaves/public-axioms-v1.lean',probe)
write('public-named-declarations-v1.json',dict(axiom_probe=names,public_proofs=22,public_definitions=5,canary_named_items=26,new_proofs=0))
print('Distinct contract bindings passed; native stabilized/proving recorded; actual retained-body audit and53 named axiom targets ready.')
