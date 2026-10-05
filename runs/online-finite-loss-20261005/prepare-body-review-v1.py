"""Freeze compiled proof/canary/axiom/dependency evidence for distinct review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
for label in ['public-body-v1-01','focused-v2-01','scoped-dependency-export-v1-01','named-axioms-v1-01']:
    assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json')
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(Path('BanditRLProof/OnlineConstraintFiniteLoss.lean'),n).encode()).hexdigest()==h
failed=run/'leaves/canary-attempt-v1.lean.txt';canary=Path('Tests/OnlineConstraintFiniteLossCanary.lean')
names=re.findall(r'(?m)^theorem\s+(\S+)',canary.read_text(encoding='utf-8'))
assert len(names)==8
for n in names:assert lean_declaration_header(failed,n)==lean_declaration_header(canary,n)
write('canary-proof-repair-v2.json',dict(original_snapshot=failed.as_posix(),original_sha256=sha(failed),
    failed_gate='focused-v1-01',repair='proof-only: instantiate constant EReal -1 to avoid coercion rewrite mismatch; remove one unnecessary simpa',
    all_eight_canary_headers_unchanged=True,production_headers_unchanged=True,successful_gate='focused-v2-01'))
graph=load('tmp/online-finite-loss-scoped-dependencies-v1.json')
assert graph['root_module']=='BanditRLProof' and graph['extraction']['source']=='compiled-environment'
assert {n['name'].rsplit('.',1)[-1] for n in graph['nodes']}==set(freeze['headers'])
assert all(n['has_value'] and n['module']=='BanditRLProof.OnlineConstraintFiniteLoss' for n in graph['nodes'])
pairs=[]
for e in graph['edges']:
    if e['target'].startswith('BanditRL.OnlineConvex.') and (e['kind']=='value' or e['also_in_value']):pairs.append([e['source'],e['target']])
assert ['BanditRL.OnlineConvex.finite_add_indicator_iff','BanditRL.OnlineConvex.extendedIndicator'] in pairs
assert ['BanditRL.OnlineConvex.effectiveDomain_add_indicator','BanditRL.OnlineConvex.effectiveDomain'] in pairs
assert ['BanditRL.OnlineConvex.effectiveDomain_add_indicator','BanditRL.OnlineConvex.extendedIndicator'] in pairs
write('compiled-dependencies-v1.json',dict(status='passed',graph_path='tmp/online-finite-loss-scoped-dependencies-v1.json',
    graph_sha256=sha('tmp/online-finite-loss-scoped-dependencies-v1.json'),fresh_export=True,scope_nodes=len(graph['nodes']),
    actual_edges=len(graph['edges']),project_proof_pairs=pairs,canary_graph_export=False,full_shared_graph_export=False,
    boundary='Actual two public proof terms from current shared compiled root; scoped direct boundary, not full-project re-export or teaching edges.'))
raw=(run/'named-axioms-v1-01.log').read_text(encoding='utf-8')
assert 'sorryAx' not in raw
axioms=re.findall(r"depends on axioms: \[([^\]]*)\]",raw)
assert len(axioms)==10
assert all(set(x.replace(' ','').split(','))<= {'propext','Classical.choice','Quot.sound'} for x in axioms)
write('proof-obligations-body-v1.json',dict(stage='proving',new_proofs_present=2,canary_proofs=8,public_headers=freeze['headers'],
    finite_terminal='compiled-local-body-review-pending',domain_support='compiled-local-body-review-pending',
    full_harness_pending=True,reader_pending=True,chapter_complete=False,goal_complete=False))
write('30_lower_worker-v1.md','Both actual new theorem bodies close the frozen terminal. Membership cases reduce the inside branch to addition by zero. Outside, all three EReal constructors exclude a finite real witness, including bottom+top=bottom. The separate domain identity uses global noBottom and add_top_of_ne_bot outside V. No desired stability/finite/domain conclusion is assumed. Eight public canaries cover distinct finite values, finite outside, top inside, bottom arbitrary V/x, empty V, real-valued domain intersection, explicit bottom leakage and false identity without noBottom. Failed coercion rewrite preserved; repair only proof bodies/all headers unchanged. Ten named checks/axiom audits and current scoped compiled proof-term graph are actual, not source-parsed dependencies. Combined full acceptance remains pending.')
write('public-body-review-packet-v1.md','''Distinct BODY review requested GPT-6 Astra / medium. Rehash all body-review-inputs-v1.json rows and prior source-contract receipt. Audit the actual two production proofs and eight public canaries, frozen headers, ten named axioms, safe guards, fresh focused build and scoped environment proof-term graph. Seek hidden assumptions, vacuity, finite/below-top conflation, silent operation change, wrong counterexample. Source criterion is unnumbered necessary direction refined to iff; arbitrary carrier generalization explicit; supporting domain hbot retained. Existing source review is contract only, never substitute for body audit. Preserve original parser failure and focused canary coercion failure; canary/body headers unchanged after repair. Scoped graph is actual two proof values from shared root, not full export/canary graph. Whole Goal active/Chapter2 countnull; integrated harness/readers/site/package not yet accepted.
Write ONLY public-body-review-v1.md/public-body-receipt-v1.json with actor.task=/root/source_reviewer, verdict, mathematical_repairs, per-target/seven-slot audit, canary nonvacuity, axiom/dependency/repair audit, reviewed_files rawSHA, report path/SHA, remaining gates. No source changes or human/external/runtime-model attestation.''')
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
paths.update(p.as_posix() for p in Path('docs/contracts/online-finite-loss-v1').rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineConstraintFiniteLoss.lean','Tests/OnlineConstraintFiniteLossCanary.lean',
    'BanditRLProof.lean','Tests.lean','tmp/online-finite-loss-scoped-dependencies-v1.json',
    'BanditRLProof/OnlineConvexExtended.lean','../research-online-ogd/tmp/pdfs/orabona-v10.pdf',
    'lean-toolchain','lakefile.lean','lake-manifest.json'])
write('body-review-inputs-v1.json',dict(rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)],scope='two new bodies/eight public canaries only'))
print('Frozen two bodies/eight unchanged-header canaries/ten standard axiom audits/current scoped graph; distinct body review pending.')
