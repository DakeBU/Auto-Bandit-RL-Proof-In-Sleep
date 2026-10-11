from delivery_guard_20261011_v3 import *
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
