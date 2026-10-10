from common import *
import copy

FINAL=RUN/'FINAL-review-v1.json'
NATIVE_PLAN=RUN/'native-acceptance-plan-v1.json'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')

def originals():
    p=load(NATIVE_PLAN);d=load(p['originals'])
    assert sha(p['originals'])==p['originals_sha256']
    result={}
    for row in d['rows']:
        raw=base64.b64decode(row['RAW_base64'])
        assert hashlib.sha256(raw).hexdigest()==row['sha256']
        result[Path(row['path'])]=raw
    assert set(result)=={ROOT/x for x in p['mutable_paths']} and len(result)==8
    return result

def render(value):
    return value.replace('{FINAL_SHA}',sha(FINAL)).replace('{SITE_HEAD}',load(RUN/'registry-inspected-v1.json')['source_commit'])

def payloads():
    p=load(NATIVE_PLAN)
    common=dict(current_leaf='source_energy_term_bound',source_family_count=1,
        production_proofs=3,definitions=0,full_canaries=2,complete_conjunct_counts=[8,3],
        source_sha256=sha(PUBLIC),Test_sha256=sha(ROOT/'Tests/OnlineAdaptiveEnergyCanary.lean'),
        FINAL_sha256=sha(FINAL),whole_Goal='active',chapter_complete=False)
    candidate=dict(common,retrospective_transport=True,
        boundary='Native append time transports earlier actual compiled candidate evidence, not contemporaneous enforcement of the entire scientific lifecycle.',
        actual_gate_receipt_sha256=sha(RUN/'combined-full-harness-v1.json'))
    accepted=dict(common,reviewer='/root/source_reviewer',
        proof_obligations_before=3,proof_obligations_after=0,
        counter_unit='Exactly three frozen production propositions; one source energy-display family, not declaration count or chapter denominator.',
        remaining_boundary=p['boundary'])
    return candidate,accepted

def expected_metadata():
    p=load(NATIVE_PLAN);b=originals();m=copy.deepcopy(json.loads(b[CONTRIBUTION].decode('utf8')))
    for key,value in p['manifest_replacements_template'].items():
        a,c=key.split('/');m[a][c]=render(value)
    result={CONTRIBUTION:(json.dumps(m,ensure_ascii=False,indent=2)+'\n').encode('utf8')}
    for rel in p['document_paths']:result[ROOT/rel]=b[ROOT/rel]+render(p['document_suffix_template']).encode('utf8')
    return result

def transition_check():
    b=originals();p=load(NATIVE_PLAN)
    for path,raw in expected_metadata().items():assert path.read_bytes()==raw,path
    def appended(path):
        raw=path.read_bytes();assert raw.startswith(b[path])
        return [json.loads(x) for x in raw[len(b[path]):].decode('utf8').splitlines() if x]
    trials=appended(RUN/'trials.jsonl');assert len(trials)==1
    t=trials[0]
    expected=dict(task=TASK,role='reviewer',kind='review',status='accepted',run_id=RUN.name,
        attempt_id='three-frozen-energy-propositions-v1',progress_class='closed-frontier',
        reviewer_validated=True,obligations_before=3,obligations_after=0,
        new_declarations=p['declarations'],verifier_evidence=[FINAL.as_posix()],
        notes=render(p['trial_notes_template']))
    for k,v in expected.items():assert t[k]==v,(k,t[k],v)
    events=appended(RUN/'lifecycle-sessions.jsonl');assert len(events)==2
    state0=json.loads(b[RUN/'lifecycle-state.json'].decode('utf8'))
    state=copy.deepcopy(state0);parent=state0['current_entry_id']
    for offset,(kind,payload) in enumerate(zip(['candidate','accepted'],payloads())):
        e=events[offset]
        assert e['session_id']==TASK and e['event_type']==kind and e['payload']==payload
        assert e['sequence']==state0['next_sequence']+offset and e['parent_id']==parent
        parent=e['entry_id']
    state.update(next_sequence=state0['next_sequence']+2,current_entry_id=parent,current_leaf='source_energy_term_bound')
    assert load(RUN/'lifecycle-state.json')==state
    return t,events

def final_fixed(after=False):
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    r=load(FINAL);assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    assert r['approved_native_plan_sha256']==sha(NATIVE_PLAN)
    for row in r['approved_native_helper_hashes']:assert sha(row['path'])==row['sha256'],row['path']
    b=originals()
    if after:transition_check()
    else:
        for path,raw in b.items():assert path.read_bytes()==raw,path
    for row in load(r['input_manifest'])['rows']:
        path=Path(row['path'])
        if after and path in b:assert hashlib.sha256(b[path]).hexdigest()==row['sha256']
        else:assert sha(path)==row['sha256'],path
    g=load(RUN/'full-harness-inspected-v1.json')
    assert g['actual_exit']==0 and g['actual_check_passed'] and g['actual_ProofGraphExport_compile_present']
    assert sha(RUN/'combined-full-harness-v1.json')==g['command_receipt_sha256']
    for k,path in [('production_sha256',PUBLIC),('Test_sha256',ROOT/'Tests/OnlineAdaptiveEnergyCanary.lean'),('root_sha256',ROOT/'BanditRLProof.lean'),('Test_root_sha256',ROOT/'Tests.lean')]:assert sha(path)==g[k]
    for rel,h in g['source_pins'].items():assert sha(ROOT/rel)==h
    return r
