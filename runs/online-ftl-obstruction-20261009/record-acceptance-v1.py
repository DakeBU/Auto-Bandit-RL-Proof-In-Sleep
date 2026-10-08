from common_accepted_v1 import *
final=accepted_fixed();targets=load(CONTRACT/'targets-v1.json')['targets']
scope='Four derived same-FTL reconciliation endpoints: exact literal all-comparator iff empirical-mean convergence; explicit dyadic support; two actual mean subsequence limits; same bounded actual learner upper/best-average0 with fixed-zero no ordinary real limit.'
remaining='Original16Chapter1 source objects/null unknown proof total, full Chapter1 reconciliation, other C1/C2, unenumerated C3-16 and necessary appendices REQUIRED. Only four derived endpoints close; Goal ACTIVE, main/live unchanged.'
boundary=dict(derived_obligations_before=4,derived_obligations_after=0,accepted_production_proofs=4,
    public_supporting_definitions=1,source_private_helpers_not_public_endpoints=8,whole_source_items_closed=0,
    chapter_complete=False,goal_complete=False,merged=False,live=False)
reg=load(RUN/'registry-v2.json')
digest=(scope+' '+remaining+' Eleven actual dyadic canaries instantiate allfour endpoints; actual prefix0,1,1,0 and causalpredictionshalf,0,half,two-thirds; bestR3five-sixths and fixed-zero R3/3negativeone-sixth. '
    'Four WHOLE VALUE witnesses/28 standard-only axiom outputs/24 selected nodes2450coalesced directTYPE_VALUEedges19requiredVALUEpairs/15fences. '
    'Actualroot9104/Tests9268/fullharness472tests7skips/checkpassed; two NONEMPTY committed-HEAD contributorbases andownshadow0. '
    'D4v1 implicit-zero failure retained/v2explicitzero repair0; initialregistry count1 ignored8private helpers, evidence-onlyv2 verifies10964COMPLETEoldrecords+5PUBLIC/8taggedsource-private, total10977; no proof/header/reader/root/pin/registryAPI change. '
    'Ten original current images inspected by formalizer anddistinctFINAL; applicablecleanlocal source'+reg['source_commit']+'. Distinctreusedautomatedactors/nohuman/external/absolute-blind/runtimeattestation. Native/post-native/draft delivery separate.')
write(RUN/'accepted-decision-v1.json',dict(verdict=final['verdict'],scope=scope,remaining_required=remaining,
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    actual_combined_gates=load(RUN/'combined-gates-v1.json'),actual_clean_site_commit=reg['source_commit'],
    mathematical_contract_version=1,stacked_base=BASE,basePR=201,native_and_draft_delivery_pending=True,**boundary))
write(RUN/'accepted-reader-discharge-v1.json',dict(requirements=load(CONTRACT/'reader-requirements-v1.json'),
    actual_FINAL_verdicts=final['reader_requirement_verdicts'],final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json')))
ledger=load(CONTRACT/'chapter-one-source-ledger-candidate-v1.json')
assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['current_bounded_FTL_obstruction_overlay']=dict(task=TASK,scope=scope,remaining_required=remaining,
    accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),original16_objects_not_marked_complete=True,
    capture_time_candidate_readers_immutable=True,bounded_same_FTL_obstruction_accepted=True,
    exact_all_comparator_converse_accepted=True,whole_Chapter1_reconciliation_gate_required=True,**boundary)
write(CONTRACT/'chapter-one-source-ledger-accepted-v1.json',ledger)
write(RUN/'memory-digest-accepted-v1.md','Task: `'+TASK+'`\n\n'+digest)
write(RUN/'retrieval-index-accepted-v1.md',digest)
write(RUN/'accepted-scoped-trials-v1.jsonl',(RUN/'trials.jsonl').read_bytes())
for cmd in ['trial-log','lifecycle-event','memory-record','retrieval-record']:
    native('accepted-help-'+cmd+'-v1',cmd,'--help')
args=['trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',RUN.name,'--attempt-id','FTL-OBSTRUCTION-FINAL-V1','--verifier-evidence',RUN/'final-reader-receipt-v1.json',
    '--harness','hierarchical','--progress-class','closed-frontier','--reviewer-validated',
    '--obligations-before','4','--obligations-after','0','--notes',digest]
for t in targets:args.extend(['--new-declaration',t['name']])
gate('accepted-reviewer-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-accepted-scoped-v1.py',*args)
own=[json.loads(s) for s in (RUN/'accepted-scoped-trials-v1.jsonl').read_text(encoding='utf8').splitlines() if s.strip()]
assert len(own)==7 and all(x['task']==TASK for x in own)
assert sum(x.get('role')=='reviewer' and x.get('status')=='accepted' for x in own)==1
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',
    json.dumps(dict(run_id=RUN.name,mathematical_contract_version=1,scope=scope,
        accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),**boundary)))
args=['frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; only four derived bounded actualFTL endpoints',
    '--leaf',TASK,'--kind','review','--statement',scope,'--file',RUN/'final-reader-review-v1.md',
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:source-reader:accepted',
    '--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending']
for t in targets:args.extend(['--dependency','lean:'+t['name']+':compiled'])
native('accepted-frontier-refresh-v1',*args)
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=load(RUN/'accepted-frontier-shadow-v1.log');assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','verified_lemma','--task',TASK,
    '--provenance-kind','source-reviewed-compiled-bounded-actual-FTL','--provenance',RUN/'accepted-decision-v1.json',
    '--status','accepted','--verifier',RUN/'final-reader-receipt-v1.json','--role','reviewer',
    '--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),
    '--output',RUN/'accepted-memory-record-v1.json')
args=['retrieval-record','--task',TASK,'--query','Actual bounded FTL ordinary-limit obstruction and exact all-comparator mean convergence iff']
for t in targets:args.extend(['--candidate',t['name']])
args.extend(['--compiled-scratch',CANARY,'--provenance',RUN/'canary-focused-v1-exit.json','--output',RUN/'accepted-retrieval-record-v1.json'])
native('accepted-retrieval-record-v1',*args)
updates={('semantic_roundtrip','remaining_semantic_delta'):'Distinct FINAL accepted; R1-R7 satisfied. '+scope+' '+remaining,
    ('graph_contribution','visual_review'):'28 standard-only axiom outputs;24selectednodes2450coalesced TYPE_VALUEedges19requiredVALUEpairs;10964completeoldregistryrecords+5PUBLIC/8source-privatehelpers,10originalimages inspected byformalizer/distinctFINAL.',
    ('verification','independent_review'):'Distinct CONTRACT189/CANARY42/BODY390/FINAL493 reviewed; D4 inference and registry-count failures retained/exact repairs verified. R1-R7 satisfied. Reusedautomatedactors/nohuman/external/absolute-blind/runtimeattestation. FINAL receipt '+sha(RUN/'final-reader-receipt-v1.json'),
    ('verification','bandit_check'):'Actualfour focused proofs/11canaries/4WHOLEVALUE/28axioms/15fences/root9104/Tests9268/fullharness472tests7skips/checkpassed; two nonempty committed-HEAD contributorbases/ownshadow0; only4derived4->0.',
    ('verification','site_build'):'Actual applicable clean local source'+reg['source_commit']+'; actual combined gate,dirtyfalse,public/canary/root/pins immutable; no deployment.',
    ('verification','site_check'):'10964COMPLETEoldsharedregistryrecords retained+4PUBLICtheorems/1PUBLICdefinition/8explicit source-private helpers,total10977;20sourcecards/fournewnotes/fourfullwrappedtypes/10actualoriginalimages andDOM/browser checks; generatedsite unmodified. Registry v1 countfailure1 retained/v2evidence-onlyrepair0.'}
assert ['.'.join(x) for x in updates]==final['permitted_future_metadata']['manifest_fields']
manifest=load(CONTRIBUTION)
for (a,k),v in updates.items():manifest[a][k]=v
CONTRIBUTION.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
append=('\n\n## Four derived bounded actual FTL endpoints accepted; draft delivery pending\n\n'+digest+'\n').encode('utf8')
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
            assert all(x.get('task',x.get('session_id'))==TASK for x in entries);b['exact_owned_entries']=entries
    bindings.append(b)
write(RUN/'accepted-metadata-bindings-v1.json',dict(rows=bindings,original_source16_unchanged=True,
    required_proof_total_null=True,global_SGB_frontier_memory_original_trials_unchanged=True,distinct_post_native_review_pending=True))
write(RUN/'proof-obligations-accepted-v1.json',dict(scope=scope,remaining_required=remaining,native_actual_commands_passed=True,**boundary))
write(RUN/'40_reviewer-decision-v1.md',digest)
accepted_fixed()
print('Actual native4->0 acceptance only; post-native/draft delivery pending, GoalACTIVE.',flush=True)
