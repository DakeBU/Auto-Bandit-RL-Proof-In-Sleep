from common import *
import ast
scripts={}
scripts['native_package_guard_prepared_20261011_v1.py']=r'''from delivery_guard_20261011_v3 import *
import copy
from types import SimpleNamespace
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import stable_id
DOCS=[ROOT/folder/(TASK+'.md') for folder in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
LOGS=[RUN/'trials.jsonl',RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json']
COUNTS=dict(frozen_production_proof_contracts=30,definitions=8,aliases=2,complete_canaries=9,reader_cards=3,source_obligation_count=None,chapter_proof_total=None,required_open_forward_containers=8,required_future_claims_open_unenumerated=6)
BOUNDARY='Bounded local adaptive OSD package only.30frozen production proof contracts are not30source obligations;8definitions+2aliases,9complete canaries and3reader cards are separately counted. No source-family count inferred. Chapter2 remains partial/accepted=false/null proof total; all8forward containers and6future claims remain required/open pending exact chapter source gates. Chapters3-16 unenumerated/null; whole Goal ACTIVE. Native events retrospectively transport prior reviewed evidence, not contemporaneous runtime enforcement of the complete scientific workflow. Postnative and independent exact-head delivery reviews remain separate. No merge/deployment/retirement.'

def bound(row):
    p=Path(row['path']);assert row.get('sha256') and sha(p)==row['sha256'],str(p)
    return p

def favorable(path,key='verdict'):
    d=load(path);assert d.get(key) in ['accepted','accepted-with-explicit-delta']
    assert not d.get('blocking_repairs',d.get('required_repairs',[]))
    return d

def validate_request(q):
    assert q['stage']=='freeze-after-actual-gates' and re.fullmatch(r'[a-zA-Z0-9_-]+',q['tag'])
    allrows=[q[k] for k in ['integration_review','full_harness_inspected','axiom_summary','potential_canary_review','algorithm_canary_review','production_review','site_binding','registry_inspected','pixel_review','contributor_inspected']]
    for row in allrows: bound(row)
    fixed(SimpleNamespace(review=Path(q['integration_review']['path']),review_sha=q['integration_review']['sha256']))
    assert Path(q['full_harness_inspected']['path'])==RUN/'full-harness-inspected-20261011-v2.json','Only authoritative harnessv2 is eligible'
    g=load(q['full_harness_inspected']['path']);assert g['actual_exit']==0 and g['actual_check_passed'] and g['actual_ProofGraphExport_compile_present']
    command=bound(g['command_receipt']);d,out=output_of(command)
    assert d['command'][-2:]==['tools/bandit.py','check'] and 'check passed' in out
    assert re.search(r'Ran \d+ tests in ',out) and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out)
    same_binding(g['source_binding']);roots=require_roots()
    axioms=load(q['axiom_summary']['path'])
    assert axioms['public_theorem_count']==39 and axioms['production_theorems']==30 and axioms['canary_theorems']==9 and len(axioms['declarations'])==39
    assert all(set(x['axioms']).issubset({'propext','Classical.choice','Quot.sound'}) for x in axioms['declarations'].values())
    same_binding(axioms['source_binding'])
    favorable(q['production_review']['path']);favorable(q['potential_canary_review']['path'],'canary_BODY_verdict');favorable(q['algorithm_canary_review']['path'],'canary_verdict')
    s=load(q['site_binding']['path']);assert s['lean_verified'] and not s['source_dirty'];same_binding(s['source_binding'])
    assert any(Path(r['path'])==Path(q['full_harness_inspected']['path']) and r['sha256']==q['full_harness_inspected']['sha256'] for r in s['full_harness'])
    m=load(Path(s['site'])/'site-manifest.json');assert m['source_commit']==s['head'] and m['lean_verified'] and not m['source_dirty']
    reg=load(q['registry_inspected']['path']);assert reg['source_commit']==s['head'] and reg['retained_complete_old_objects'] and reg['new_nodes']==40 and reg['source_cards']==19
    pix=favorable(q['pixel_review']['path'])
    assert q['original_pixel_images'],'Actual original pixel files required'
    for row in q['original_pixel_images']: bound(row)
    contributor=load(q['contributor_inspected']['path']);assert contributor['nonempty_substantive_diff'];same_binding(contributor['source_binding'])
    mapping=load(load(PLAN)['mapping'][0]['path']);proofs=[r['name'] for r in mapping['canonical_declarations'] if r['kind']=='theorem']
    assert len(proofs)==30 and len(set(proofs))==30
    assert set(proofs).issubset(axioms['declarations'])
    return dict(source_binding=g['source_binding'],root_receipts=roots,site_head=s['head'],proof_contracts=proofs,gate_rows=rows([Path(r['path']) for r in allrows]+[Path(r['path']) for r in q['original_pixel_images']]))

def render(value,final,site_head):
    return value.replace('{FINAL_SHA}',sha(final)).replace('{SITE_HEAD}',site_head)

def load_plan(path):
    p=load(path);assert p['scope']=='bounded-package-native-plan' and p['counts']==COUNTS
    assert p['manifest_mutation']==False and p['mathematical_source_mutation']==False and p['coverage_mutation']==False
    for row in p['helpers']+p['support']:bound(row)
    return p

def final_guard(plan_path,final_path,after=False):
    p=load_plan(plan_path);f=favorable(final_path)
    assert f['approved_native_plan_sha256']==sha(plan_path)
    assert f['approved_native_helper_hashes']==p['helpers']
    assert f['original_pixels_personally_reviewed']==True
    assert f['counter_unit']=='30 frozen production proof contracts; source/chapter denominator unknown'
    im=bound(f['input_manifest']);assert sha(im)==p['final_inputs_sha256']
    validate_request(load(p['request']['path']));same_binding(p['source_binding'])
    mutable={r['path']:r for r in p['mutable_originals']}
    for row in load(im)['rows']:
        if after and row['path'] in mutable:assert row['sha256']==mutable[row['path']]['sha256']
        else:bound(row)
    if not after:
        for row in p['mutable_originals']:bound(row)
        assert not Path(p['new_accepted_contract']).exists()
    return p,f

def payloads(p,final):
    shared=dict(current_leaf='bounded-adaptive-osd-package',package=TASK,counts=COUNTS,FINAL_sha256=sha(final),whole_Goal='ACTIVE',chapter_complete=False,source_obligation_count=None)
    return [dict(shared,retrospective_transport=True,evidence_manifest_sha256=p['final_inputs_sha256'],boundary=BOUNDARY),dict(shared,proof_contracts_before=30,proof_contracts_after=0,counter_unit='30 frozen production proof contracts; source/chapter denominator unknown',boundary=BOUNDARY)]

def predict_state(p,final):
    state=copy.deepcopy(json.loads(base64.b64decode(next(r for r in p['mutable_originals'] if r['path']==(RUN/'lifecycle-state.json').as_posix())['RAW_base64'])))
    expected=[]
    for kind,payload in zip(['candidate','accepted'],payloads(p,final)):
        identity=dict(session_id=TASK,sequence=state['next_sequence'],parent_id=state['current_entry_id'],event_type=kind,payload=payload)
        eid=stable_id('entry',identity);expected.append(dict(identity,entry_id=eid))
        state.update(next_sequence=state['next_sequence']+1,current_entry_id=eid,current_leaf=payload['current_leaf'])
    return state,expected

def transition_check(p,final):
    before={r['path']:base64.b64decode(r['RAW_base64']) for r in p['mutable_originals']}
    for path in DOCS:
        assert path.read_bytes()==before[path.as_posix()]+render(p['document_suffix_template'],final,p['site_head']).encode('utf8')
    def added(path):
        raw=path.read_bytes();assert raw.startswith(before[path.as_posix()])
        return [json.loads(x) for x in raw[len(before[path.as_posix()]):].decode('utf8').splitlines() if x]
    trials=added(RUN/'trials.jsonl');assert len(trials)==1
    t=trials[0];assert t['task']==TASK and t['role']=='reviewer' and t['status']=='accepted' and t['reviewer_validated']==True
    assert t['obligations_before']==30 and t['obligations_after']==0 and t['new_declarations']==p['proof_contracts']
    assert t['verifier_evidence']==[Path(final).as_posix()] and t['notes']==BOUNDARY
    state,expected=predict_state(p,final);events=added(RUN/'lifecycle-sessions.jsonl');assert len(events)==2
    for actual,want in zip(events,expected):
        for k,v in want.items():assert actual[k]==v,(k,actual[k],v)
    assert load(RUN/'lifecycle-state.json')==state
    same_binding(p['source_binding'])
    return dict(trial=t,events=events,state=state)
'''
scripts['freeze-native-package-plan-prepared-20261011-v1.py']=r'''from native_package_guard_prepared_20261011_v1 import *
parser=argparse.ArgumentParser();parser.add_argument('--request',type=Path,required=True);a=parser.parse_args()
q=load(a.request);verified=validate_request(q);tag=q['tag']
plan_path=RUN/('native-package-plan-'+tag+'.json');inputs_path=RUN/('native-package-FINAL-inputs-'+tag+'.json')
assert not plan_path.exists() and not inputs_path.exists()
mutable=DOCS+LOGS
originals=[dict(path=p.as_posix(),sha256=sha(p),RAW_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mutable]
assert len(originals)==7
# Capture source/metadata fingerprints WITHOUT changing them. Imported helpers are immutable support.
helper_names=['native_package_guard_prepared_20261011_v1.py','freeze-native-package-plan-prepared-20261011-v1.py','execute-native-package-prepared-20261011-v1.py','prepare-postnative-transition-prepared-20261011-v1.py']
helpers=rows([RUN/name for name in helper_names]);support=rows([RUN/'common.py',RUN/'native-scoped.py',RUN/'delivery_guard_20261011_v3.py',RUN/'delivery-preparation-config-20261011-v1.json',ROOT/'tools/bandit.py',ROOT/'tools/abrl_lifecycle.py'])
extra=[bound(row) for row in q['additional_exact_inputs']]
all_inputs=[Path(r['path']) for r in verified['gate_rows']+verified['source_binding']+helpers+support]+mutable+[a.request]+extra
write(inputs_path,dict(rows=rows(all_inputs),scope='Actual pre-native FINAL inputs; seven mutable originals retained; source/manifest/readers/coverage immutable; no FINAL verdict inferred'))
suffix='\n\n## Bounded adaptive OSD package accepted locally\n\nDistinct FINAL `{FINAL_SHA}`; verified clean local site candidate `{SITE_HEAD}`. Exactly30 frozen production proof contracts were reviewed for this bounded package; native counter30->0 is not a source-obligation or chapter denominator.8definitions+2aliases,9complete canaries and3reader cards remain separately classified. Actual gate/reader/registry/pixel evidence and source deltas live in the new package accepted contract. The existing contribution manifest remains the frozen reviewed candidate snapshot, not silently rewritten as current gate evidence. '+BOUNDARY+'\n'
p=dict(scope='bounded-package-native-plan',request=rows([a.request])[0],counts=COUNTS,source_binding=verified['source_binding'],site_head=verified['site_head'],proof_contracts=verified['proof_contracts'],mutable_originals=originals,document_paths=[x.as_posix() for x in DOCS],document_suffix_template=suffix,new_accepted_contract=(CONTRACT/('package-accepted-'+tag+'.json')).as_posix(),helpers=helpers,support=support,final_inputs=inputs_path.as_posix(),final_inputs_sha256=sha(inputs_path),manifest_mutation=False,mathematical_source_mutation=False,coverage_mutation=False,tag=tag,boundary=BOUNDARY)
write(plan_path,p)
write(RUN/('native-package-FINAL-packet-'+tag+'.md'),'Review all exact inputs, actual authoritative harnessv2/root/Tests,39standard-axiom declarations,9complete canaries, source/BODY reviews, site/registry and ALL original images. Personally view original pixels. Assess the exact native plan/helpers: only4own-doc appends,1trial append,2events and exact lifecycle state change; new OWN acceptedcontract/evidence only; no source/manifest/reader/coverage changes. Counter30->0 refers only to the30named frozen production proof contracts. Return a distinct FINAL verdict with blocking_repairs, input_manifest path/hash, approved_native_plan_sha256, approved_native_helper_hashes, original_pixels_personally_reviewed and counter_unit exactly "30 frozen production proof contracts; source/chapter denominator unknown". Approving this plan does not execute native acceptance. Postnative review and S3 exact state exemption remain separate. '+BOUNDARY)
print(plan_path.as_posix())
'''
scripts['execute-native-package-prepared-20261011-v1.py']=r'''from native_package_guard_prepared_20261011_v1 import *
parser=argparse.ArgumentParser();parser.add_argument('--plan',type=Path,required=True);parser.add_argument('--final',type=Path,required=True);a=parser.parse_args()
p,f=final_guard(a.plan,a.final);tag=p['tag']
# Durable create-only start: partial execution is never automatically replayed.
write(RUN/('native-package-started-'+tag+'.json'),dict(plan=rows([a.plan]),FINAL=rows([a.final]),state_before=rows([RUN/'lifecycle-state.json']),boundary='No automatic retry. On failure retain all output and obtain a bounded recovery plan.'))
state_expected,events_expected=predict_state(p,a.final)
write(RUN/('native-state-expected-'+tag+'.json'),dict(before=next(r for r in p['mutable_originals'] if r['path']==(RUN/'lifecycle-state.json').as_posix()),expected_after_object=state_expected,expected_two_events_without_timestamps=events_expected,scope='Prospective semantic exact transition derived from frozen state+FINAL; actual RAW hashes only after native execution'))
for kind,payload in [('candidate',payloads(p,a.final)[0])]:
    event('native-package-'+kind+'-'+tag,kind,payload)
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','thirty-frozen-adaptive-osd-proof-contracts-'+tag,'--progress-class','closed-frontier','--reviewer-validated','--obligations-before','30','--obligations-after','0']
for name in p['proof_contracts']:args+=['--new-declaration',name]
args+=['--notes',BOUNDARY,'--verifier-evidence',a.final.as_posix()]
capture('native-package-trial-'+tag,*args)
event('native-package-accepted-'+tag,'accepted',payloads(p,a.final)[1])
for path in DOCS:
    before=base64.b64decode(next(r for r in p['mutable_originals'] if r['path']==path.as_posix())['RAW_base64'])
    assert path.read_bytes()==before
    path.write_bytes(before+render(p['document_suffix_template'],a.final,p['site_head']).encode('utf8'))
contract=dict(package=TASK,status='accepted-local-bounded-package',FINAL=rows([a.final]),native_plan=rows([a.plan]),counts=COUNTS,proof_contracts=p['proof_contracts'],source_binding=p['source_binding'],site_build_head=p['site_head'],scope=BOUNDARY,chapter_accepted=False,Goal_status='ACTIVE',native_transport='retrospective evidence transport, not contemporaneous whole-workflow enforcement',postnative_review='pending',exact_head_delivery_review='pending',contribution_manifest='Frozen candidate snapshot deliberately unchanged; actual gates/acceptance recorded here.')
write(Path(p['new_accepted_contract']),contract)
transition=transition_check(p,a.final)
final_guard(a.plan,a.final,after=True)
write(RUN/('native-package-actual-transition-'+tag+'.json'),dict(plan=rows([a.plan]),FINAL=rows([a.final]),accepted_contract=rows([Path(p['new_accepted_contract'])]),transition=transition,mutable_before=p['mutable_originals'],mutable_after=rows([Path(r['path']) for r in p['mutable_originals']]),source_binding_unchanged=True,source_manifest_reader_coverage_unchanged=True,postnative_review='required',S3_current_inspector='Will reject nonprefix lifecycle-state change until exact narrow postnative transition review and separately versioned inspector. No broad exemption granted.'))
'''
scripts['prepare-postnative-transition-prepared-20261011-v1.py']=r'''from native_package_guard_prepared_20261011_v1 import *
parser=argparse.ArgumentParser();parser.add_argument('--plan',type=Path,required=True);parser.add_argument('--final',type=Path,required=True);a=parser.parse_args()
p,f=final_guard(a.plan,a.final,after=True);transition=transition_check(p,a.final);tag=p['tag']
actual=RUN/('native-package-actual-transition-'+tag+'.json');assert load(actual)['source_binding_unchanged']
state_path=RUN/'lifecycle-state.json';relative=state_path.relative_to(ROOT).as_posix()
H0=p['site_head'];raw0=subprocess.check_output(['git','show',H0+':'+relative],cwd=ROOT)
proposal=dict(scope='Proposed single-path S3 evidence transition exemption; NOT approved or executable',allowed_path=relative,site_head_H0=H0,evidence_head_H1=None,H0_before_sha256=hashlib.sha256(raw0).hexdigest(),H0_before_RAW_base64=base64.b64encode(raw0).decode('ascii'),actual_after_sha256=sha(state_path),actual_after_RAW_base64=base64.b64encode(state_path.read_bytes()).decode('ascii'),actual_native_transition=rows([actual]),native_plan=rows([a.plan]),FINAL=rows([a.final]),exact_mutation='Only lifecycle-state: next_sequence+2, chained deterministic current_entry_id, current_leaf bounded-adaptive-osd-package; all other fields unchanged as checked by native transition. If H0before differs from pre-native snapshot, reviewer must audit the entire intervening chain separately.',no_blanket_allow=True,requires='Independent postnative review of exact before/after+events; freeze actual H1 later; separately reviewed S3 inspector version accepting only this exactpath+hashpair+H0/H1. Existing S3v4 remains fail-closed.')
write(RUN/('S3-single-state-transition-proposed-'+tag+'.json'),proposal)
files=[Path(r['path']) for r in load(p['final_inputs'])['rows']]+[a.plan,a.final,actual,Path(p['new_accepted_contract']),RUN/('S3-single-state-transition-proposed-'+tag+'.json')]+DOCS+LOGS
write(RUN/('postnative-package-inputs-'+tag+'.json'),dict(rows=rows(files),source_binding=p['source_binding'],scope='Actual postnative bytes; pre-native originals retained in plan; no approval inferred'))
write(RUN/('postnative-package-packet-'+tag+'.md'),'Review actual native trial/events/state and4exact-prefix task-doc appends against frozen originals; new acceptedcontract and immutable full sourcebinding/manifest/readers/coverage.30proofcontracts,9canaries,3cards do not establish source/chapter denominator. Review proposed SINGLE lifecycle-state hashpair exemption separately, trace full H0->actualstate chain if needed, and require actual H1 binding plus a separately reviewed S3 inspector. No broad RUN allowance; original S3v4 stays failclosed. Delivery remains new draft OSD PR targeting adaptive-energy; PR217 unchanged. '+BOUNDARY)
print('Actual postnative packet and UNAPPROVED exact state-transition proposal prepared.')
'''
for name,s in scripts.items():ast.parse(s,filename=name);write(RUN/name,s)
request=dict(stage='freeze-after-actual-gates',tag='REPLACE_WITH_UNIQUE_TAG',integration_review=dict(path=(RUN/'fresh-exact-integration-review-20261011-v5.json').as_posix(),sha256=None),full_harness_inspected=dict(path=(RUN/'full-harness-inspected-20261011-v2.json').as_posix(),sha256=None),axiom_summary=dict(path=None,sha256=None),potential_canary_review=dict(path=(RUN/'potential-canary-BODY-minimum-review-v1.json').as_posix(),sha256=None),algorithm_canary_review=dict(path=(RUN/'fresh-canary-BODY-review-20261011-v1.json').as_posix(),sha256=None),production_review=dict(path=(RUN/'fresh-production-source-review-20261011-v1.json').as_posix(),sha256=None),site_binding=dict(path=None,sha256=None),registry_inspected=dict(path=None,sha256=None),pixel_review=dict(path=None,sha256=None),contributor_inspected=dict(path=None,sha256=None),original_pixel_images=[],additional_exact_inputs=[])
write(RUN/'native-package-request-TEMPLATE-20261011-v1.json',request)
write(RUN/'native-package-helpers-prepared-20261011-v1.json',dict(scripts=rows([RUN/name for name in scripts]),support=rows([RUN/'common.py',RUN/'native-scoped.py',RUN/'delivery_guard_20261011_v3.py',RUN/'delivery-preparation-config-20261011-v1.json',ROOT/'tools/bandit.py',ROOT/'tools/abrl_lifecycle.py']),request_template=rows([RUN/'native-package-request-TEMPLATE-20261011-v1.json']),ast_parse=True,executed=False,actual_plan_frozen=False,counts=dict(production_proof_contracts=30,definitions=8,aliases=2,complete_canaries=9,reader_cards=3,source_obligation_count=None,chapter_proof_total=None),immutable=['Lean production/tests/roots','contribution manifest','reader JSON/coverage','source pins','whole sourcebinding pathset/bytes'],future_mutable_preexisting=['4own taskdocs exactprefix append','trials.jsonl append1review','lifecycle-sessions.jsonl append2events','lifecycle-state.json exact independently checked transition'],S3='Single state path exacthashpair proposal only after actual transition; independentpostnative review and reviewedinspector required; no blanket exemption',scope='Prepared templates only; parent freezes actual request/plan/FINALinputs after authoritativeharnessv2+rootTests39axioms9canaries reviewed/site/registry/pixels; distinct FINAL before execution. No native action/commit/push executed.'))
write(RUN/'native-package-preparation-explanation-20261011-v1.md','''# Prepared bounded package acceptance workflow

All four helpers are unexecuted; only Python AST syntax was checked. The request is an intentionally incomplete template. Parent must create a new request populated with actual paths and SHA256s after the authoritative full-harness v2, completed root/Tests,39 standard-axiom theorem records,9 complete canaries and source/BODY reviews, contributor gates, clean local site, full registry retention and original-pixel review exist.

1. Future freeze helper validates those actual receipts and source bindings, then creates an exact native plan, seven original byte snapshots and FINAL input manifest. It does not accept anything.
2. Distinct FINAL reviewer must personally inspect source/statement/proof/gates and original images; approve exact plan/helper hashes and the explicit30-production-proof-contract counter. This count is not a source-family or chapter count.
3. Future native executor records a create-only start sentinel, retrospective candidate and accepted events, one accepted30->0 proof-contract trial,4own-document suffixes, and a NEW own accepted-package contract. It never edits the contribution manifest, mathematical Lean, roots, reader metadata or coverage after the validated gates/site. A partial failure is preserved and is not automatically retried.
4. Postnative preparation checks the actual transition, preserves before/after state bytes and proposes a SINGLE lifecycle-state path/hashpair exemption for S3. Approval of that exemption and a separately versioned inspector remain necessary; S3v4 continues to reject the nonprefix state change. Actual evidence headH1 must be bound after the parent-authorized evidence commit; the site remains explicitly built atH0.

Counts stay separate:30 frozen production proof contracts;8definitions+2aliases;9complete canaries;3reader cards. No source-family count is invented. Source-obligation/chapter denominators remain null, all8Chapter2 forward containers and6future mathematical claims stay open, Goal ACTIVE. Native transport is retrospective bookkeeping of already reviewed evidence. No merge/deployment/retirement or final exact-head delivery acceptance follows merely from these helpers.
''')
print('Prepared4nativehelpers+request template/explanation; noactualplan/nativeexecution.')
