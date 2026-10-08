from common_accepted_v2 import *

final=accepted_fixed()
targets=load(CONTRACT/'targets-v1.json')['targets']
scope='Four derived ambient-completion proofs only: actual real measurable-version producer, one same-process all-time bounded history family, original current-target independence and exact original IID expected-fixed excess for every natural horizon.'
remaining='Original16 Chapter1 source objects/null unknown proof total, general causal stochastic-kernel realization, other source-required information/completion constructions, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE, main/live unchanged.'
boundary=dict(derived_obligations_before=4,derived_obligations_after=0,accepted_production_proofs=4,
    whole_source_items_closed=0,chapter_complete=False,goal_complete=False,merged=False,live=False)
write(RUN/'accepted-decision-v1.json',dict(verdict=final['verdict'],scope=scope,remaining_required=remaining,
    mathematical_contract_version=1,presentation_version=1,stacked_base=BASE,basePR=198,
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    actual_combined_gates=load(RUN/'combined-gates-v1.json'),
    actual_clean_site_commit=load(RUN/'registry-v2.json')['source_commit'],
    reader_capture_candidate_status_preserved=True,native_and_draft_delivery_pending=True,**boundary))
write(RUN/'accepted-reader-discharge-v1.json',dict(requirements=load(CONTRACT/'reader-requirements-v1.json'),
    actual_FINAL_verdicts=final['reader_requirement_verdicts'],final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json')))
ledger=load(CONTRACT/'chapter-one-source-ledger-draft-v1.json')
assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['current_completed_leaf_overlay']=dict(task=TASK,scope=scope,remaining_required=remaining,
    accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),original16_objects_not_marked_complete=True,
    capture_time_candidate_readers_immutable=True,**boundary)
write(CONTRACT/'chapter-one-source-ledger-accepted-v1.json',ledger)
digest='Task: `'+TASK+'`\n\n'+scope+' '+remaining+' Four focused public proofs and11actual canary proofs;56 standard axiom records;52selected compiled nodes2614coalesced TYPE_VALUE edges18required directVALUEpairs. Actual root9101/Tests9262/fullharness passed (exact test/skip counts in raw log), both contributor bases and own shadow passed. Applicable clean local site preserves10938COMPLETE old nodes plus4actual declarations;10original current images separately viewed by formalizer/source reviewer. CONTRACT175/BODY285/FINAL current receipt, exactR1-R7; proof/type-printer/receipt-schema failures retained. Distinct reused staged automated actors, no absolute blind/human/external/runtime attestation. Native/post-native/draft delivery separately recorded.'
write(RUN/'memory-digest-accepted-v1.md',digest)
write(RUN/'retrieval-index-accepted-v1.md',digest)
args=['trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',RUN.name,'--attempt-id','COMPLETED-CAUSAL-FINAL-V1','--verifier-evidence',RUN/'final-reader-receipt-v1.json',
    '--harness','hierarchical','--progress-class','closed-frontier','--reviewer-validated',
    '--obligations-before','4','--obligations-after','0','--notes',digest]
for t in targets:args.extend(['--new-declaration',t['name']])
native('accepted-reviewer-trial-v1',*args)
own=[json.loads(s) for s in (ROOT/'runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip() and json.loads(s).get('task')==TASK]
assert sum(x.get('role')=='reviewer' and x.get('status')=='accepted' for x in own)==1
write(RUN/'accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(x,ensure_ascii=False) for x in own))
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',
    json.dumps(dict(run_id=RUN.name,mathematical_contract_version=1,scope=scope,
        accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),**boundary)))
args=['frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; four derived ambient-completion proofs only',
    '--leaf',TASK,'--kind','review','--statement',scope,'--file',RUN/'final-reader-review-v1.md',
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:source-reader:accepted',
    '--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending']
for t in targets:args.extend(['--dependency','lean:'+t['name']+':compiled'])
native('accepted-frontier-refresh-v1',*args)
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=load(RUN/'accepted-frontier-shadow-v1.log');assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','verified_lemma','--task',TASK,
    '--provenance-kind','source-reviewed-compiled-completed-causal-producer','--provenance',RUN/'accepted-decision-v1.json',
    '--status','accepted','--verifier',RUN/'final-reader-receipt-v1.json','--role','reviewer',
    '--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),
    '--output',RUN/'accepted-memory-record-v1.json')
native('accepted-retrieval-record-v1','retrieval-record','--task',TASK,'--query','Actual completed-information real versions, original causal history/current independence/IID expected fixed excess',
    '--candidate',targets[0]['name'],'--candidate',targets[1]['name'],'--candidate',targets[2]['name'],'--candidate',targets[3]['name'],
    '--compiled-scratch',CANARY,'--provenance',RUN/'canary-focused-v1-exit.json','--output',RUN/'accepted-retrieval-record-v1.json')
manifest=load(MANIFEST)
updates={('semantic_roundtrip','remaining_semantic_delta'):'Actual FINAL accepted; exactR1-R7 satisfied. '+scope+' '+remaining,
    ('graph_contribution','visual_review'):'56standard-only axiom outputs;52selected nodes2614coalesced TYPE_VALUE edges18required directVALUEpairs;10938COMPLETE old registry nodes preserved plus4new Online Learning declarations;10original formalizer/distinctFINAL pixel inspections.',
    ('verification','independent_review'):'Distinct CONTRACT175/BODY285/FINAL exact current fixed inputs;R1-R7 satisfied. Reused automated actors, no human/external/absolute blind/runtime attestation. Receipt '+sha(RUN/'final-reader-receipt-v1.json'),
    ('verification','bandit_check'):'Actual four focused/whole-type VALUE/56axiom/fences/root9101/Tests9262/fullharness; both contributor bases/ownshadow passed. Closes4derived completion obligations only; exact tests/skips in raw evidence.',
    ('verification','site_build'):'Actual applicable clean local source '+load(RUN/'registry-v2.json')['source_commit']+'; combined gate passed, dirtyfalse, production/canary/pins immutable; no deployment.',
    ('verification','site_check'):'10938COMPLETE old shared registry nodes preserved plus4actual Online Learning declarations, full four headers and10original formalizer/distinctFINAL pixels reviewed; genuine v2 browser/DOM/capture evidence; actual v1 overflow retained.'}
assert ['.'.join(x) for x in updates]==final['permitted_future_metadata']['manifest_fields']
for (a,k),v in updates.items():manifest[a][k]=v
MANIFEST.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
append=('\n\n## Four derived completed-information obligations accepted; draft delivery pending\n\n'+digest+'\n').encode('utf8')
for p in APPEND_METADATA:p.write_bytes(p.read_bytes()+append)
rows=[]
for r in load(RUN/'FINAL-metadata-snapshots-v1.json'):
    p=Path(r['live_path']);before=Path(r['snapshot']).read_bytes();after=p.read_bytes()
    assert sha(r['snapshot'])==r['sha256']
    row=dict(path=p.as_posix(),original_snapshot=r['snapshot'],original_sha256=r['sha256'],current_sha256=sha(p))
    if p==MANIFEST:
        old=json.loads(before.decode('utf8'));now=load(p)
        row['exact_six_fields']=[dict(field=a+'.'+k,old=old[a][k],new=now[a][k]) for a,k in updates]
        for a,k in updates:assert now[a][k]!=old[a][k];now[a][k]=old[a][k]
        assert now==old
    else:
        assert after.startswith(before);suffix=after[len(before):]
        row['suffix_sha256']=hashlib.sha256(suffix).hexdigest()
        if p in APPEND_METADATA:assert suffix==append;row['exact_owned_suffix']=suffix.decode('utf8')
        elif p.suffix=='.jsonl':
            entries=[json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
            assert all(x.get('task',x.get('session_id'))==TASK for x in entries)
            row['exact_owned_entries']=entries
        else:assert p.name=='MANIFEST.md' and not suffix
    rows.append(row)
write(RUN/'accepted-metadata-bindings-v1.json',dict(rows=rows,exact_owned_suffixes=True,
    original_source16_unchanged=True,required_proof_total_null=True,globalSGB_unchanged=True,
    distinct_post_native_review_pending=True))
write(RUN/'proof-obligations-accepted-v1.json',dict(scope=scope,remaining_required=remaining,native_actual_commands_passed=True,**boundary))
write(RUN/'native-acceptance-overlay-v1.json',dict(status='actual native commands passed; post-native audit/draft pending',**boundary))
write(RUN/'40_reviewer-decision-v1.md',digest)
accepted_fixed()
print('Four derived completed-information obligations accepted by actual scoped native commands; distinct post-native/draft pending; whole Goal active.',flush=True)
