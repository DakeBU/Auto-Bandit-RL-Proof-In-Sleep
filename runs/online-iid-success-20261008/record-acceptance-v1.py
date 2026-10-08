from common_accepted_v1 import *

final=accepted_fixed()
scope='Four frozen C1 terminals only: generic centered-total success iff, actual private-seed strict-history IID policy criterion, actual unknown-law meanPredict expected-fixed 4log upper without independence and ordinary normalized zero/little-o under IID.'
remaining=load(RUN/'reader-proposal-v1.json')['boundary']
boundary=dict(source_package_accepted=True,chapter_complete=False,goal_complete=False,merged=False,live=False,
    new_public_proofs=4,new_public_definitions=0,bounded_terminals_closed=4,whole_source_items_closed=0)
write(RUN/'accepted-reader-discharge-v1.json',dict(status='passed',requirements=load(RUN/'stabilized-contract-v1.json')['reader_requirements'],
    actual_FINAL_verdicts=final['reader_requirement_verdicts'],final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json')))
write(RUN/'accepted-decision-v1.json',dict(status=final['verdict'],scope=scope,remaining_required=remaining,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),contract_version=1,exact_base_PR=195,exact_base_head=BASE,
    body_bindings=load(RUN/'body-bindings-v1.json'),combined_gates=load(RUN/'combined-gates-v1.json'),
    contributor_log_sha256=sha(RUN/'contributor-candidate-committed-v2.log'),applicable_site_commit=load(RUN/'registry-v1.json')['source_commit'],
    registry_sha256=sha(RUN/'registry-v1.json'),pixel_record_sha256=sha(RUN/'pixel-review-v1.json'),
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),native_acceptance_pending=True,PR_delivery_pending=True,**boundary))
ledger=load(CONTRACT/'chapter-one-source-ledger-draft-v1.json')
original_items=ledger['maintext_items']
assert len(original_items)==16 and ledger['required_proof_leaf_total'] is None
ledger['version']=2
ledger['own_overlay']=dict(task=TASK,status='bounded-four-terminal-semantic-accepted; native/draft delivery separately recorded',
    source_obligations=['C1-EQ1.1-1.2'],derived_application='Actual unknown-law meanPredict expected-fixed IID stochastic success from source Theorem1.3',
    evidence=(RUN/'accepted-decision-v1.json').as_posix(),scope=scope,remaining_required=remaining,whole_source_item_complete=False)
assert ledger['maintext_items']==original_items
write(CONTRACT/'chapter-one-source-ledger-accepted-v2.json',ledger)
digest=TASK+' '+scope+' '+remaining+' Actual 45 named kernel checks/14 direct VALUE pairs/14 nondegenerate canary proofs; actual root9099/Tests9257/fullharness472skip7/stacked contributor5paths1contract. Clean applicable local site1cffe4be,10931 old nodes preserved+4 new,ten original current panels ROOT and distinct FINAL inspected. Distinct staged automated reviews; no human/external/absolute blind/runtime attestation. Frozen bounded progress4->0 only. Raw failures/eleven byte-bound log or historical snapshot diff exceptions retained, zero executable/production/Test/reader/contract exception. Native acceptance/draft delivery separately recorded, whole Goal remains active.'
write(RUN/'memory-digest-accepted-v1.md',digest)
write(RUN/'retrieval-index-accepted-v1.md',digest)
statement=load(RUN/'S004-v1-fence.json');terminal=PRE+'meanPredict_iid_success'
native('accepted-reviewer-trial-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',RUN.name,'--attempt-id','IID-SUCCESS-V1','--statement-hash',statement['statement_hash'],'--new-declaration',terminal,
    '--verifier-evidence',RUN/'final-reader-receipt-v1.json','--harness','hierarchical','--progress-class','terminal',
    '--reviewer-validated','--obligations-before','4','--obligations-after','0','--notes',digest)
own=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip() and json.loads(s).get('task')==TASK]
assert sum(x.get('status')=='accepted' and x.get('role')=='reviewer' for x in own)==1
write(RUN/'accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(x,ensure_ascii=False) for x in own))
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=1,accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),scope_only=scope,**boundary)))
native('accepted-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1–16; bounded C1 IID success four terminals only',
    '--leaf',TASK,'--kind','lean','--statement',statement['statement'],'--declaration',terminal,'--file',PUBLIC,
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+PRE+'meanPredict_expectedFixed_upper:compiled',
    '--dependency','lean:'+PRE+'centered_total_sublinear_iff_average:compiled','--dependency','review:source-reader:accepted',
    '--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=load(RUN/'accepted-frontier-shadow-v1.log')
assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','verified_lemma','--task',TASK,
    '--provenance-kind','source-reviewed-compiled-bounded-IID-success','--provenance',RUN/'accepted-decision-v1.json',
    '--declaration',terminal,'--file',PUBLIC,'--status','accepted','--verifier',RUN/'final-reader-receipt-v1.json',
    '--role','reviewer','--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),
    '--output',RUN/'accepted-memory-record-v1.json')
native('accepted-retrieval-record-v1','retrieval-record','--task',TASK,'--query','Actual unknown-law meanPredict ordinary IID stochastic success',
    '--candidate',PRE+'centered_total_sublinear_iff_average','--candidate',terminal,'--compiled-scratch',CANARY,
    '--provenance',RUN/'canary-focused-build-v1-exit.json','--output',RUN/'accepted-retrieval-record-v1.json')
m=load(MANIFEST)
m['semantic_roundtrip']['remaining_semantic_delta']+=' Separate FINAL accepted; exact R1–R8 satisfied for this bounded four-terminal package. Required full source model, five old audits and chapter/program obligations remain open.'
m['verification']['independent_review']='Distinct staged CONTRACT88/BODY128/FINAL511 accepted-with-explicit-delta; exact R1–R8 satisfied. FINAL receipt '+sha(RUN/'final-reader-receipt-v1.json')+'; reused automated actors, no human/external/absolute blind/runtime attestation.'
m['verification']['bandit_check']='Actual shared root9099/Tests9257/fullharness472tests7skips/stacked committed contributor5productionpaths1contract/scoped shadow passed; oldmain5audits unwaived.'
m['verification']['site_build']='Applicable clean local source1cffe4be362928fb80bfb9a0a7b0b77049840c3c, dirtyfalse/Leanverifiedtrue; public/canary/pins unchanged from combined gates; no deployment.'
m['verification']['site_check']='10931 prior registry IDs/URLs/hashes preserved+4new; four complete note/catalogue headers; current formulas/DOM/ten ROOT and distinct FINAL original pixel reviews passed.'
m['graph_contribution']['visual_review']='45 selected compiled kernel constants/3325 TYPE_VALUE occurrences/14 required direct VALUE pairs; four new shared registry nodes and ten current original panels independently inspected.'
MANIFEST.write_bytes((json.dumps(m,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
append=('\n\n## Bounded IID success package accepted; draft delivery pending\n\n'+digest+'\n').encode('utf8')
for p in APPEND_METADATA: p.write_bytes(p.read_bytes()+append)
rows=[]
for record in load(RUN/'FINAL-metadata-snapshots-v1.json'):
    p=Path(record['live_path']);before=Path(record['snapshot']).read_bytes();after=p.read_bytes()
    assert sha(record['snapshot'])==record['sha256']
    row=dict(path=p.resolve().as_posix(),original_snapshot=record['snapshot'],original_sha256=record['sha256'],current_sha256=sha(p))
    if p.resolve()==MANIFEST.resolve():
        old=json.loads(before.decode('utf8'));now=load(p)
        row['exact_six_fields']=[dict(field=a+'.'+k,old=old[a][k],new=now[a][k]) for a,k in SIX_FIELDS]
        for a,k in SIX_FIELDS: assert now[a][k]!=old[a][k];now[a][k]=old[a][k]
        assert now==old
    else:
        assert after.startswith(before);suffix=after[len(before):]
        row['suffix_sha256']=hashlib.sha256(suffix).hexdigest()
        if p.resolve() in {x.resolve() for x in APPEND_METADATA}:
            assert suffix==append;row['exact_owned_suffix']=suffix.decode('utf8')
        elif p.suffix=='.jsonl':
            entries=[json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
            assert all(x.get('task',x.get('session_id'))==TASK for x in entries)
            row['exact_owned_entries']=entries
        else: assert p.name=='MANIFEST.md' and not suffix
    rows.append(row)
write(RUN/'accepted-metadata-bindings-v1.json',dict(rows=rows,exact_owned_suffixes=True,original_source16_unchanged=True,
    required_proof_total_null=True,globalSGB_unchanged=True,distinct_post_native_review_pending=True))
write(RUN/'40_reviewer-decision-v1.md',digest)
write(RUN/'proof-obligations-accepted-v1.json',dict(contract_version=1,frozen_targets=4,compiled_targets=4,accepted_targets=4,
    remaining_bounded_mathematical_terminals=0,chapter1_source_objects=16,required_proof_leaf_total=None,
    remaining_required=remaining,PR_delivery_pending=True,**boundary))
write(RUN/'native-acceptance-overlay-v1.json',dict(status='actual-native-passed',one_accepted_reviewer_trial=True,
    obligations_before=4,obligations_after=0,obligation_count_scope='Only four frozen bounded terminals',
    globalSGB_unchanged=True,PR_delivery_pending=True,**boundary))
accepted_fixed()
print('Actual bounded native package acceptance recorded; distinct metadata audit/draft delivery pending; total Goal active.')
