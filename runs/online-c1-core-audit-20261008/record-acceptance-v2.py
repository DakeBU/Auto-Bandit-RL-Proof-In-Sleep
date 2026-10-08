from common_accepted_v2 import *

final=accepted_fixed()
scope='Five legacy core source-module audits only, twelve reused exact public proofs, zero new production theorems; original headers/bodies preserved.'
remaining='Original sixteen Chapter1 source objects/null proof total, full universal stochastic-kernel/completed-information/AE-factorization coverage, remaining C1/C2, unenumerated C3-16 and necessary appendices remain required. Whole Goal active; main/live unchanged.'
boundary=dict(five_source_audits_accepted=True,source_audits_before=5,source_audits_after=0,
    new_production_proofs=0,whole_source_items_closed=0,chapter_complete=False,goal_complete=False,merged=False,live=False)
write(RUN/'accepted-decision-v2.json',dict(verdict=final['verdict'],scope=scope,remaining_required=remaining,
    contract_version=2,stacked_base=BASE,basePR=196,final_receipt_sha256=sha(RUN/'final-reader-receipt-v2.json'),
    public_sha256={p.as_posix():sha(p) for p in MODULES},canary_sha256=sha(CANARY),
    actual_combined_gates=load(RUN/'combined-gates-v1.json'),actual_clean_site_commit=load(RUN/'registry-v2.json')['source_commit'],
    reader_capture_candidate_status_preserved=True,native_and_draft_delivery_pending=True,**boundary))
write(RUN/'accepted-reader-discharge-v2.json',dict(requirements=load(CONTRACT/'reader-requirements-v1.json'),
    actual_FINAL_verdicts=final['reader_requirement_verdicts'],final_receipt_sha256=sha(RUN/'final-reader-receipt-v2.json')))
ledger=load(CONTRACT/'chapter-one-source-ledger-draft-v1.json')
assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['own_current_audit_overlay']=dict(task=TASK,scope=scope,accepted_decision=(RUN/'accepted-decision-v2.json').as_posix(),
    historical_Foundations_acceptance_preserved=True,original16_objects_not_marked_complete=True,
    capture_time_candidate_readers_immutable=True,remaining_required=remaining,**boundary)
write(CONTRACT/'chapter-one-source-ledger-accepted-v3.json',ledger)
digest='Task: `'+TASK+'`\n\n'+scope+' '+remaining+' Actual standard-axiom68 / compiler graph70nodes4134occurrences19VALUEpairs; seven historical+34new canary proofs/4testdefinitions; root9099/Tests9258/fullharness472skip7 stable v2, original failure preserved. Both stacked and origin/main contributors passed; exact raw log/historical helper exceptions only. Clean applicable local site preserves10935 IDs/URLs/hashes,26original images personally inspected by ROOT and distinct source reviewer. CONTRACT93/BODY185/repaired FINAL504; rejected FINAL419/F1 retained automated staged reviews; reused history disclosed, no human/external/absolute blindness/runtime attestation. Only five source-audit obligations5->0; new mathematical production proofs0. Native metadata and draft delivery separately recorded.'
write(RUN/'memory-digest-accepted-v2.md',digest)
write(RUN/'retrieval-index-accepted-v2.md',digest)
args=['trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',RUN.name,'--attempt-id','CORE-AUDIT-V2','--verifier-evidence',RUN/'final-reader-receipt-v2.json',
    '--harness','hierarchical','--progress-class','retrieval-reuse','--reviewer-validated',
    '--obligations-before','5','--obligations-after','0','--notes',digest]
for row in load(CONTRACT/'targets-v2.json')['targets']:args.extend(['--reused-declaration',row['name']])
native('accepted-reviewer-trial-v2',*args)
own=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip() and json.loads(s).get('task')==TASK]
assert sum(x.get('role')=='reviewer' and x.get('status')=='accepted' for x in own)==1
write(RUN/'accepted-scoped-trials-v2.jsonl','\n'.join(json.dumps(x,ensure_ascii=False) for x in own))
native('accepted-lifecycle-v2','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=2,scope=scope,accepted_decision=(RUN/'accepted-decision-v2.json').as_posix(),**boundary)))
native('accepted-frontier-refresh-v2','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; five source module audits only',
    '--leaf',TASK,'--kind','review','--statement',scope,'--file',RUN/'final-reader-review-v2.md',
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:source-reader:accepted',
    '--dependency','lean:'+PRE+'iid_meanPredict_excess:compiled','--dependency','lean:'+PRE+'history_policy_loss_ge_variance:compiled',
    '--trials',RUN/'accepted-scoped-trials-v2.jsonl','--output',RUN/'accepted-frontier-v2.json','--shadow-status','pending')
native('accepted-frontier-shadow-v2','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v2.jsonl',
    '--memory-digest',RUN/'memory-digest-accepted-v2.md','--frontier',RUN/'accepted-frontier-v2.json')
shadow=load(RUN/'accepted-frontier-shadow-v2.log');assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v2','memory-record','--type','source_fact','--task',TASK,
    '--provenance-kind','source-reviewed-compiled-existing-module-audit','--provenance',RUN/'accepted-decision-v2.json',
    '--status','accepted','--verifier',RUN/'final-reader-receipt-v2.json','--role','reviewer',
    '--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),'--output',RUN/'accepted-memory-record-v2.json')
native('accepted-retrieval-record-v2','retrieval-record','--task',TASK,'--query','Five legacy core exact prefix/variance/history audits',
    '--candidate',PRE+'lemma_1_2','--candidate',PRE+'iid_meanPredict_excess','--candidate',PRE+'history_policy_loss_ge_variance',
    '--compiled-scratch',CANARY,'--provenance',RUN/'canary-focused-build-v3-exit.json','--output',RUN/'accepted-retrieval-record-v2.json')
manifest=load(MANIFEST)
updates={('semantic_roundtrip','remaining_semantic_delta'):'Separate repaired FINAL504; rejected FINAL419/F1 retained accepted with exact R1-R8 satisfied. '+scope+' '+remaining,
    ('graph_contribution','visual_review'):'68 actual axiom outputs;70 compiler nodes4134TYPE_VALUE occurrences19required VALUE pairs;10935old registry IDs/URLs/hashes preserved,zero new;26ROOT and distinct FINAL original current panel inspections passed.',
    ('verification','independent_review'):'Distinct staged CONTRACT93/BODY185/repaired FINAL504; rejected FINAL419/F1 retained accepted-with-explicit-delta; exactR1-R8 satisfied. Reused automated actors/history disclosed; no human/external/absolute blindness/runtime attestation. FINAL receipt '+sha(RUN/'final-reader-receipt-v2.json'),
    ('verification','bandit_check'):'Actual root9099/Tests9258/fullharness472skip7 stablev2 and exact focused archive assertion; first failedharness retained. Both stacked and origin/main contributor gates pass; scoped shadow passes; five audited source obligations only.',
    ('verification','site_build'):'Actual applicable clean local source '+load(RUN/'registry-v2.json')['source_commit']+';Leanverifiedtrue,dirtyfalse,unchanged proofs/canary/pins; no deployment.',
    ('verification','site_check'):'10935old registry IDs/URLs/statementhashes preserved,zero new nodes;12full types/formulas/folded reader headers,26current original ROOT/distinctFINAL pixels checked.'}
assert ['.'.join(x) for x in updates]==final['permitted_future_metadata']['manifest_fields']
for (a,k),v in updates.items():manifest[a][k]=v
MANIFEST.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
append=('\n\n## Five scoped core source audits accepted; draft delivery pending\n\n'+digest+'\n').encode('utf8')
for p in APPEND_METADATA:p.write_bytes(p.read_bytes()+append)
rows=[]
for r in load(RUN/'FINAL-metadata-snapshots-v2.json'):
    p=Path(r['live_path']);before=Path(r['snapshot']).read_bytes();after=p.read_bytes();assert sha(r['snapshot'])==r['sha256']
    row=dict(path=p.as_posix(),original_snapshot=r['snapshot'],original_sha256=r['sha256'],current_sha256=sha(p))
    if p.resolve()==MANIFEST.resolve():
        old=json.loads(before.decode('utf8'));now=load(p)
        row['exact_six_fields']=[dict(field=a+'.'+k,old=old[a][k],new=now[a][k]) for a,k in updates]
        for a,k in updates:assert now[a][k]!=old[a][k];now[a][k]=old[a][k]
        assert now==old
    else:
        assert after.startswith(before);suffix=after[len(before):];row['suffix_sha256']=hashlib.sha256(suffix).hexdigest()
        if p.resolve() in {x.resolve() for x in APPEND_METADATA}:assert suffix==append;row['exact_owned_suffix']=suffix.decode('utf8')
        elif p.suffix=='.jsonl':
            entries=[json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
            assert all(x.get('task',x.get('session_id'))==TASK for x in entries);row['exact_owned_entries']=entries
        else:assert p.name=='MANIFEST.md' and not suffix
    rows.append(row)
write(RUN/'accepted-metadata-bindings-v2.json',dict(rows=rows,exact_owned_suffixes=True,original_source16_unchanged=True,
    required_proof_total_null=True,globalSGB_unchanged=True,distinct_post_native_review_pending=True))
write(RUN/'proof-obligations-accepted-v2.json',dict(scope=scope,remaining_required=remaining,native_actual_commands_passed=True,**boundary))
write(RUN/'native-acceptance-overlay-v2.json',dict(status='actual native commands passed; post-native audit/draft pending',**boundary))
write(RUN/'40_reviewer-decision-v2.md',digest)
accepted_fixed()
print('Five source audits accepted by actual scoped native commands; distinct post-native audit/draft pending, whole Goal active.')
