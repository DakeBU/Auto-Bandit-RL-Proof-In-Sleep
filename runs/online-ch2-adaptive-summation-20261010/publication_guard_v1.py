from candidate_guard_v4 import *
import copy

NATIVE_PLAN=RUN/'native-acceptance-plan-v1.json'
FINAL=RUN/'FINAL-review-v1.json'
FINAL_INPUTS=RUN/'FINAL-inputs-v1.json'

def final_review_fixed():
    r=load(FINAL)
    assert r['package_verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(FINAL_INPUTS)==r['input_manifest_sha256']
    assert r['approved_native_plan_sha256']==sha(NATIVE_PLAN)
    assert r['approved_native_helper_hashes']==load(NATIVE_PLAN)['helpers']
    for row in r['approved_native_helper_hashes']: assert sha(row['path'])==row['sha256'],row['path']
    return r

def originals():
    plan=load(NATIVE_PLAN);d=load(plan['originals'])
    assert sha(plan['originals'])==plan['originals_sha256']
    result={}
    for r in d['rows']:
        b=base64.b64decode(r['before_raw_base64']);assert hashlib.sha256(b).hexdigest()==r['before_sha256']
        result[Path(r['path'])]=b
    assert set(result)=={ROOT/p for p in plan['mutable_paths']}
    return result

def templates():
    plan=load(NATIVE_PLAN);head=load(RUN/'registry-inspected-v1.json')['source_commit']
    render=lambda s:s.replace('{FINAL_SHA}',sha(FINAL)).replace('{SITE_HEAD}',head)
    return {tuple(k.split('/')):render(v) for k,v in plan['manifest_replacements_template'].items()},render(plan['document_suffix_template'])

def payloads():
    plan=load(NATIVE_PLAN)
    candidate=dict(current_leaf='lemma_4_13',bounded_stage='candidate',actual_candidate_evidence_sha256=sha(RUN/'candidate-stage-evidence-v1.json'),retrospective_runtime_append_after_FINAL=True,scope='Actual candidate evidence predates FINAL; this append is retrospective transport, not source acceptance or chapter closure.',chapter_complete=False,goal_complete=False)
    accepted=dict(current_leaf='lemma_4_13',scope=plan['boundary'],terminal=plan['terminal'],new_production_proofs=1,new_definitions=0,full_public_canaries=2,source_family_count=1,bounded_obligations_before=1,bounded_obligations_after=0,FINAL_sha256=sha(FINAL),recorded_by='/root from distinct /root/source_reviewer FINAL',source_container_closed=False,chapter_proof_total=None,chapter_complete=False,goal_complete=False,post_native_review='pending',delivery='pending')
    return candidate,accepted

def native_transition_check():
    before=originals();plan=load(NATIVE_PLAN);replacements,suffix=templates()
    manifest=copy.deepcopy(json.loads(before[CONTRIBUTION].decode('utf8')))
    for (a,b),v in replacements.items():manifest[a][b]=v
    assert CONTRIBUTION.read_bytes()==(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8')
    for rel in plan['document_paths']:
        p=ROOT/rel;assert p.read_bytes()==before[p]+suffix.encode('utf8'),p
    trial=RUN/'trials.jsonl';events=RUN/'lifecycle-sessions.jsonl';state=RUN/'lifecycle-state.json'
    assert trial.read_bytes().startswith(before[trial]) and events.read_bytes().startswith(before[events])
    tr=[json.loads(s) for s in trial.read_bytes()[len(before[trial]):].decode('utf8').splitlines()]
    assert len(tr)==1;tr=tr[0]
    assert (tr['task'],tr['role'],tr['kind'],tr['status'],tr['reviewer_validated'])==(TASK,'reviewer','review','accepted',True)
    assert tr['new_declarations']==[plan['terminal']['declaration']] and (tr['obligations_before'],tr['obligations_after'])==(1,0)
    assert tr['verifier_evidence']==[str(FINAL)] and tr['notes']==plan['trial_notes_template'].replace('{FINAL_SHA}',sha(FINAL))
    evs=[json.loads(s) for s in events.read_bytes()[len(before[events]):].decode('utf8').splitlines()]
    assert len(evs)==2
    oldstate=json.loads(before[state].decode('utf8'));parent=oldstate['current_entry_id']
    for i,(ev,kind,payload) in enumerate(zip(evs,['candidate','accepted'],payloads())):
        identity=dict(session_id=TASK,sequence=oldstate['next_sequence']+i,parent_id=parent,event_type=kind,payload=payload)
        assert all(ev[k]==v for k,v in identity.items()) and ev['entry_id']==lifecycle.stable_id('entry',identity)
        parent=ev['entry_id']
    expected=copy.deepcopy(oldstate);expected.update(next_sequence=oldstate['next_sequence']+2,current_entry_id=parent,current_leaf='lemma_4_13')
    assert load(state)==expected
    return before,tr,evs

def publication_fixed(after_native=False):
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    allowed={r['path']:r for r in load(CONTRACT/'exact-integration-plan-v1.json')['rows']}
    for row in load(RUN/'baseline-v1.json')['rows']:
        assert sha(row['path'])==(allowed[row['path']]['after_sha256'] if row['path'] in allowed else row['sha256']),row['path']
    actual_gates_fixed();final_review_fixed()
    if not after_native:
        candidate_fixed()
        for row in load(FINAL_INPUTS)['rows']:assert sha(row['path'])==row['sha256'],row['path']
    else:
        before,_,_=native_transition_check()
        for row in load(FINAL_INPUTS)['rows']:
            p=Path(row['path'])
            if p in before:assert hashlib.sha256(before[p]).hexdigest()==row['sha256']
            else:assert sha(p)==row['sha256'],p
