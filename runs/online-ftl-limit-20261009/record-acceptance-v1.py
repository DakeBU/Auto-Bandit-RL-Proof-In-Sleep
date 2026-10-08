from common_accepted_v1 import *

final=accepted_fixed()
targets=load(CONTRACT/'targets-v1.json')['targets']
scope='Five derived same-process FTL hinges: all-real empty-horizon loss-gap/decomposition; unit-stream best average zero and signed fixed-limit equivalence; explicit empirical-mean convergence produces literal LimitNoRegret.'
remaining='Concrete bounded oscillating actual-FTL obstruction and exact all-comparator converse remain REQUIRED. Original16Chapter1 source objects/null unknown proof total, other C1/C2, unenumerated C3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE, main/live unchanged.'
boundary=dict(derived_obligations_before=5,derived_obligations_after=0,accepted_production_proofs=5,
    whole_source_items_closed=0,chapter_complete=False,goal_complete=False,merged=False,live=False)
digest=(scope+' '+remaining+' Twelve actual alternating-binary canaries instantiate all five terminals; proved mean/count and fixed-zero limit -1/4. Five whole-type VALUE witnesses,29 standard-only axiom outputs,24 selected nodes2676 coalesced TYPE_VALUEedges16 required directVALUEpairs and17 native fences. Actual root9103/Tests9266/fullharness-v2 472tests7skips; both contributor bases and ownshadow passed. First fullharness-v1 untracked-Lean rejection1 retained and staging-only repair0. F1 fence/render/capture-prerequisite failures retained. Applicable clean local site preserves10959complete registry records plus exactly5production nodes; twelve original images inspected by formalizer/distinctFINAL. Distinct reused automated roles; no absolute-blind/human/external/runtime-model attestation. Native/post-native/draft delivery separately recorded.')
write(RUN/'accepted-decision-v1.json',dict(verdict=final['verdict'],scope=scope,remaining_required=remaining,
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    actual_combined_gates=load(RUN/'combined-gates-v1.json'),actual_clean_site_commit=load(RUN/'registry-v1.json')['source_commit'],
    mathematical_contract_version=1,stacked_base=BASE,basePR=200,native_and_draft_delivery_pending=True,**boundary))
write(RUN/'accepted-reader-discharge-v1.json',dict(requirements=load(CONTRACT/'reader-requirements-v1.json'),
    actual_FINAL_verdicts=final['reader_requirement_verdicts'],final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json')))
ledger=load(CONTRACT/'chapter-one-source-ledger-candidate-v1.json')
assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['current_FTL_limit_hinge_overlay']=dict(task=TASK,scope=scope,remaining_required=remaining,
    accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),original16_objects_not_marked_complete=True,
    capture_time_candidate_readers_immutable=True,bounded_oscillating_same_FTL_obstruction_required=True,
    exact_all_comparator_converse_required=True,**boundary)
write(CONTRACT/'chapter-one-source-ledger-accepted-v1.json',ledger)
write(RUN/'memory-digest-accepted-v1.md','Task: `'+TASK+'`\n\n'+digest)
write(RUN/'retrieval-index-accepted-v1.md',digest)
write(RUN/'accepted-scoped-trials-v1.jsonl',(RUN/'trials.jsonl').read_bytes())
args=['trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',RUN.name,'--attempt-id','FTL-LIMIT-FINAL-V1','--verifier-evidence',RUN/'final-reader-receipt-v1.json',
    '--harness','hierarchical','--progress-class','closed-frontier','--reviewer-validated',
    '--obligations-before','5','--obligations-after','0','--notes',digest]
for t in targets:args.extend(['--new-declaration',t['name']])
gate('accepted-reviewer-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-accepted-scoped-v1.py',*args)
own=[json.loads(s) for s in (RUN/'accepted-scoped-trials-v1.jsonl').read_text(encoding='utf8').splitlines() if s.strip()]
assert len(own)==7 and all(x['task']==TASK for x in own)
assert sum(x.get('role')=='reviewer' and x.get('status')=='accepted' for x in own)==1
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',
    json.dumps(dict(run_id=RUN.name,mathematical_contract_version=1,scope=scope,
        accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),**boundary)))
args=['frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; only five derived actualFTL limit hinges',
    '--leaf',TASK,'--kind','review','--statement',scope,'--file',RUN/'final-reader-review-v1.md',
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:source-reader:accepted',
    '--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending']
for t in targets:args.extend(['--dependency','lean:'+t['name']+':compiled'])
native('accepted-frontier-refresh-v1',*args)
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=load(RUN/'accepted-frontier-shadow-v1.log');assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','verified_lemma','--task',TASK,
    '--provenance-kind','source-reviewed-compiled-actual-FTL-limit','--provenance',RUN/'accepted-decision-v1.json',
    '--status','accepted','--verifier',RUN/'final-reader-receipt-v1.json','--role','reviewer',
    '--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),
    '--output',RUN/'accepted-memory-record-v1.json')
args=['retrieval-record','--task',TASK,'--query','Actual strict-past FTL signed comparator identity and ordinary-limit criterion']
for t in targets:args.extend(['--candidate',t['name']])
args.extend(['--compiled-scratch',CANARY,'--provenance',RUN/'canary-focused-v1-exit.json','--output',RUN/'accepted-retrieval-record-v1.json'])
native('accepted-retrieval-record-v1',*args)
updates={('semantic_roundtrip','remaining_semantic_delta'):'Distinct FINAL accepted; R1-R7 satisfied. '+scope+' '+remaining,
    ('graph_contribution','visual_review'):'29 standard-only axiom outputs;24 selected nodes2676 coalesced TYPE_VALUEedges16 required directVALUEpairs.10959complete oldregistry records plus exactly5production targets;12original formalizer/distinctFINAL image inspections.',
    ('verification','independent_review'):'Distinct CONTRACT48/CANARY24/BODY287/FINAL414 reviewed. R1-R7 satisfied. Reused automated actors; no human/external/absolute-blind/runtime attestation. FINAL receipt '+sha(RUN/'final-reader-receipt-v1.json'),
    ('verification','bandit_check'):'Actual five focused bodies/twelvecanaries/wholeVALUE/29axioms/17fences/root9103/Tests9266/fullharness-v2 472tests7skips; both contributorbases/ownshadow passed. Initialharness1 retained, staging-only repair0. Only5derived obligations close.',
    ('verification','site_build'):'Actual applicable clean local source '+load(RUN/'registry-v1.json')['source_commit']+'; combined gate passed, dirtyfalse, public/canary/pins immutable; no deployment.',
    ('verification','site_check'):'10959COMPLETE oldregistry records preserved plus exactly5production nodes;19sourcecards/fivenotes/five fullheaders and12original images inspected, actual DOM/browser evidence. Generated site unmodified.'}
assert ['.'.join(x) for x in updates]==final['permitted_future_metadata']['manifest_fields']
manifest=load(CONTRIBUTION)
for (a,k),v in updates.items():manifest[a][k]=v
CONTRIBUTION.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
append=('\n\n## Five derived actual FTL limit obligations accepted; draft delivery pending\n\n'+digest+'\n').encode('utf8')
for p in APPEND_METADATA:p.write_bytes(p.read_bytes()+append)
bindings=[]
for r in load(RUN/'FINAL-metadata-snapshots-v1.json'):
    p=Path(r['live_path']);before=Path(r['snapshot']).read_bytes();assert sha(r['snapshot'])==r['sha256']
    if sha(p)==r['sha256']:continue
    b=dict(path=p.as_posix(),snapshot=r['snapshot'],original_sha256=r['sha256'],current_sha256=sha(p))
    if p==CONTRIBUTION:
        old=json.loads(before.decode('utf8'));now=load(p)
        b['exact_six_fields']=[dict(field=a+'.'+k,old=old[a][k],new=now[a][k]) for a,k in updates]
        for a,k in updates:now[a][k]=old[a][k]
        assert now==old
    else:
        after=p.read_bytes();assert after.startswith(before);suffix=after[len(before):]
        b['suffix_sha256']=hashlib.sha256(suffix).hexdigest()
        if p in APPEND_METADATA:assert suffix==append;b['exact_owned_suffix']=suffix.decode('utf8')
        else:
            assert p==ROOT/'runs/lifecycle_sessions.jsonl'
            entries=[json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
            assert all(x.get('task',x.get('session_id'))==TASK for x in entries)
            b['exact_owned_entries']=entries
    bindings.append(b)
write(RUN/'accepted-metadata-bindings-v1.json',dict(rows=bindings,original_source16_unchanged=True,
    required_proof_total_null=True,global_SGB_frontier_memory_and_original_trials_unchanged=True,
    distinct_post_native_review_pending=True))
write(RUN/'proof-obligations-accepted-v1.json',dict(scope=scope,remaining_required=remaining,native_actual_commands_passed=True,**boundary))
write(RUN/'40_reviewer-decision-v1.md',digest)
accepted_fixed()
print('Actual native acceptance of five derived hinges only; distinct post-native/draft pending.',flush=True)
