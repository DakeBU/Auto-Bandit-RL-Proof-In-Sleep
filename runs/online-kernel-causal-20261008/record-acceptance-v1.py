from common_accepted_v1 import *

final=accepted_fixed()
targets=load(CONTRACT/'targets-v2.json')['targets']
scope='Five derived behavioral-kernel proofs only: one sampler before all laws/horizons, actual finite causal recursion and same-process prefix consistency, derived joint law, AE conditional law and every-horizon IID expected-fixed excess/nonnegativity.'
remaining='Original16 Chapter1 source objects/null unknown proof total; arbitrary-protocol/filtration/private-state reduction and action-dependent adaptive environments are not covered. Other required source/information constructions, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE, main/live unchanged.'
boundary=dict(derived_obligations_before=5,derived_obligations_after=0,accepted_production_proofs=5,
    whole_source_items_closed=0,chapter_complete=False,goal_complete=False,merged=False,live=False)
write(RUN/'accepted-decision-v1.json',dict(verdict=final['verdict'],scope=scope,remaining_required=remaining,
    mathematical_contract_version=1,presentation_version=1,stacked_base=BASE,basePR=199,
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    actual_combined_gates=load(RUN/'combined-gates-v1.json'),
    actual_clean_site_commit=load(RUN/'registry-v2.json')['source_commit'],
    reader_capture_candidate_status_preserved=True,native_and_draft_delivery_pending=True,**boundary))
write(RUN/'accepted-reader-discharge-v1.json',dict(requirements=load(CONTRACT/'reader-requirements-v1.json'),
    actual_FINAL_verdicts=final['reader_requirement_verdicts'],final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json')))
ledger=load(CONTRACT/'chapter-one-source-ledger-draft-v1.json')
assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['current_kernel_leaf_overlay']=dict(task=TASK,scope=scope,remaining_required=remaining,
    accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),original16_objects_not_marked_complete=True,
    capture_time_candidate_readers_immutable=True,**boundary)
write(CONTRACT/'chapter-one-source-ledger-accepted-v1.json',ledger)
digest='Task: `'+TASK+'`\n\n'+scope+' '+remaining+' Five focused public bodies and13canary proofs;57standard-only axiom records,52selected nodes3106coalesced TYPE_VALUEedges22requireddirectVALUEpairs. Combined root9102/Tests9264/fullharness472tests7skips; both contributor bases and ownshadow passed. Applicable clean local site preserves10942complete old records plus17module nodes:5terminals,8context definitions,4private helpers.12original pixels inspected by formalizer/distinctFINAL. CONTRACT104/retrieval16/BODY350/EOF22/registry-repair13/FINAL separately bound; all failure logs retained. Reused distinct automated actors; no absolute-blind/human/external/runtime attestation. Native/post-native/delivery separately recorded.'
write(RUN/'memory-digest-accepted-v1.md',digest)
write(RUN/'retrieval-index-accepted-v1.md',digest)
args=['trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',RUN.name,'--attempt-id','KERNEL-CAUSAL-FINAL-V1','--verifier-evidence',RUN/'final-reader-receipt-v1.json',
    '--harness','hierarchical','--progress-class','closed-frontier','--reviewer-validated',
    '--obligations-before','5','--obligations-after','0','--notes',digest]
for t in targets:args.extend(['--new-declaration',t['name']])
native('accepted-reviewer-trial-v1',*args)
own=[json.loads(s) for s in (ROOT/'runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip() and json.loads(s).get('task')==TASK]
assert sum(x.get('role')=='reviewer' and x.get('status')=='accepted' for x in own)==1
write(RUN/'accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(x,ensure_ascii=False) for x in own))
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',
    json.dumps(dict(run_id=RUN.name,mathematical_contract_version=1,scope=scope,
        accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),**boundary)))
args=['frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; five derived behavioral-kernel proofs only',
    '--leaf',TASK,'--kind','review','--statement',scope,'--file',RUN/'final-reader-review-v1.md',
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:source-reader:accepted',
    '--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending']
for t in targets:args.extend(['--dependency','lean:'+t['name']+':compiled'])
native('accepted-frontier-refresh-v1',*args)
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=load(RUN/'accepted-frontier-shadow-v1.log');assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','verified_lemma','--task',TASK,
    '--provenance-kind','source-reviewed-compiled-kernel-causal-producer','--provenance',RUN/'accepted-decision-v1.json',
    '--status','accepted','--verifier',RUN/'final-reader-receipt-v1.json','--role','reviewer',
    '--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),
    '--output',RUN/'accepted-memory-record-v1.json')
native('accepted-retrieval-record-v1','retrieval-record','--task',TASK,'--query','Actual causal behavioral-kernel realization, same-process joint/conditional laws and IID expected fixed excess',
    '--candidate',targets[0]['name'],'--candidate',targets[1]['name'],'--candidate',targets[2]['name'],'--candidate',targets[3]['name'],'--candidate',targets[4]['name'],
    '--compiled-scratch',CANARY,'--provenance',RUN/'canary-focused-v4-exit.json','--output',RUN/'accepted-retrieval-record-v1.json')
manifest=load(MANIFEST)
updates={('semantic_roundtrip','remaining_semantic_delta'):'Actual FINAL accepted; exactR1-R7 satisfied. '+scope+' '+remaining,
    ('graph_contribution','visual_review'):'57standard-only axiom outputs;52selected nodes3106coalesced TYPE_VALUE edges22required directVALUEpairs;10942COMPLETE old registry nodes preserved plus17module nodes (five frozen terminal theorems,8context definitions,4private helpers);12original formalizer/distinctFINAL pixel inspections.',
    ('verification','independent_review'):'Distinct CONTRACT104/BODY350/FINAL exact current fixed inputs;R1-R7 satisfied. Reused automated actors, no human/external/absolute blind/runtime attestation. Receipt '+sha(RUN/'final-reader-receipt-v1.json'),
    ('verification','bandit_check'):'Actual five focused/whole-type VALUE/57axiom/fences/root9102/Tests9264/fullharness; both contributor bases/ownshadow passed. Closes5derived behavioral-kernel obligations only; exact tests/skips in raw evidence.',
    ('verification','site_build'):'Actual applicable clean local source '+load(RUN/'registry-v2.json')['source_commit']+'; combined gate passed, dirtyfalse, production/canary/pins immutable; no deployment.',
    ('verification','site_check'):'10942complete old registry records preserved,17module nodes=5terminals+8context definitions+4private helpers; five headers and12original pixels inspected. Original5-node expectation audit1 retained; exact reviewed17-node repair0. Actual browser/DOM evidence, no site mutation.'}
assert ['.'.join(x) for x in updates]==final['permitted_future_metadata']['manifest_fields']
for (a,k),v in updates.items():manifest[a][k]=v
MANIFEST.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
append=('\n\n## Five derived behavioral-kernel obligations accepted; draft delivery pending\n\n'+digest+'\n').encode('utf8')
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
print('Five derived behavioral-kernel obligations accepted by actual scoped native commands; distinct post-native/draft pending; whole Goal active.',flush=True)
