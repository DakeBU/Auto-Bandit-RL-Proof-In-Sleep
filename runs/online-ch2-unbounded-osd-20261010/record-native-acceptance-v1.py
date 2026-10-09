from publication_guard_v2 import *
import copy
fixed()
final=RUN/'FINAL-review-v1.json';review=load(final)
assert review['package_verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']
assert sha(review['report'])==review['report_sha256'] and sha(RUN/'FINAL-inputs-v1.json')==review['input_manifest_sha256']
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
targets=load(CONTRACT/'stabilized-v1.json')['targets'];names=[t['name'] for t in targets];assert len(names)==11
docs=[ROOT/d/(TASK+'.md') for d in ['proof-obligations','research-wiki/retrieval-index']]
native=[RUN/n for n in ['trials.jsonl','lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
mutable=[CONTRIBUTION,*docs,*native];before={p:p.read_bytes() if p.exists() else None for p in mutable}
write(RUN/'pre-native-exact-bytes-v1.json',dict(FINAL_sha256=sha(final),rows=[dict(path=p.as_posix(),exists=raw is not None,sha256=hashlib.sha256(raw).hexdigest() if raw is not None else None,before_raw_base64=base64.b64encode(raw).decode('ascii') if raw is not None else None) for p,raw in before.items()]))
bound=('Eleven frozen proof terminals and four source witness definitions close the required Chapter2 Theorem5.4 dependency: actual canonical affine selector/step/prefix, exact scalar regret identity, genuine sum-integral/horizon proof, unit-direction embedding and positive-dimensional source existential; exact phi range and left limit1-log2>=.3. '
 'Two complete7/9conjunct canaries prove actual T2 states/strictly positive decreasing steps/regret1, and T64 E2D nonzero update/regularity/threshold/printed bound/256/15<=R/17<R/full source existential. T2/T64 are different horizon-specific loss streams. Four individually selected compiled conjunct VALUES retain the required NEW source proofs. '
 'No desired regret or trajectory premise, future-aware learner, minimax-all-learners bound, bounded domain or source phi continuity at1. Nontrivial E is source-implicit and necessary; classical canonical selector is not claimed executable/measurable. '
 'Eleven proof terminals are not eleven printed source results or a chapter denominator. All8Chapter2forward containers required/open pending dedicated source reconciliation and chapter gates; Chapter2partial/null,Ch3-16unenumerated/null; wholeChapters1-16GoalACTIVE. No merge/deploy/main/live/CI/retirement.')
g=load(RUN/'full-harness-inspected-v1.json');reg=load(RUN/'registry-inspected-v1.json')
write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nBounded distinct FINAL '+sha(final)+'. Actual combined/full harness hashes '+sha(RUN/'full-harness-inspected-v1.json')+'; clean local SITEv1 source '+reg['source_commit']+' preserves11026completeoldregistryobjects+15canonicalproduction=11041.32actual desktop originals personally reviewed byroot and distinctFINAL; localfile, notHTTP/live/mobile. Native11->0 only11frozenproofterminals; postnative/concrete delivery pending.\n')
notes=bound+' Distinct source_reviewer FINAL '+sha(final)+'. Native11->0 ONLY these eleven frozen proof terminals; postnative/delivery pending.'
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','eleven-frozen-unbounded-OSD-proofs-v1','--progress-class','closed-frontier','--reviewer-validated','--obligations-before','11','--obligations-after','0','--notes',notes,'--verifier-evidence',final]
for n in names:args+=['--new-declaration',n]
capture('native-acceptance-trial-v1',*args)
payload=dict(scope=bound,terminals=[dict(declaration=n,statement_hash=load(CONTRACT/('frozen-'+n.rsplit('.',1)[1]+'-v1.json'))['statement_hash']) for n in names],source_definitions=4,FINAL_sha256=sha(final),recorded_by='/root from distinct /root/source_reviewer decision',bounded_obligations_before=11,bounded_obligations_after=0,chapter_proof_total=None,chapter_complete=False,goal_complete=False,post_native_review='pending',delivery='pending')
event('native-acceptance-event-v1','accepted',payload)
c=load(CONTRIBUTION);oldc=copy.deepcopy(c)
allowed=[('semantic_roundtrip','remaining_semantic_delta'),('verification','independent_review'),('graph_contribution','visual_review'),('verification','site_check')]
c['semantic_roundtrip']['remaining_semantic_delta']=bound+' Distinct staged neutral/CONTRACT/BODY/plan/helper/bounded FINAL '+sha(final)+'. Related automated actor history disclosed; no human/external/absolute-blind/runtime attestation. OWN postnative/delivery pending.'
c['verification']['independent_review']='Distinct bounded FINAL '+sha(final)+' accepts eleven frozen proof terminals/four definitions/two FULL public canaries, combined gates, shared registry and32original desktop pixels. All source/chapter/Goal boundaries explicit. OWN postnative/concrete delivery pending.'
c['graph_contribution']['visual_review']='17public/selected nodes,3240coalesced directTYPE_VALUE presences,24requiredVALUEpairs/4individually selected numeric/existential branches. All11026completeoldregistryobjects unchanged+15canonicalproduction=11041. Actual localfile desktop1440/16sourceguideformulas/zeroerrors/foldedLean/built-inwrap/32originals root+distinctFINAL. NotHTTP/live/allviewports/perBookduplicates/fulltransitive/sourcecount.'
c['verification']['site_check']='Actual site check and complete11026oldregistryobjects unchanged+15canonicalproduction=11041;13sourcecards. Actualfile desktop16sourceguideformulas/zeroerrors/foldedLean/wrap/32originals personally viewed byroot and distinct bounded FINAL '+sha(final)+'. Local-only, notHTTP/live/mobile/allviewports; postnative/delivery pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nBounded FINAL accepted: '+bound+' FINAL SHA '+sha(final)+'. OWN native11->0 only11proofterminals; postnative/draftPR pending. Historical stage-pending entries remain historical.\n'
for p in docs:p.write_bytes(before[p]+suffix.encode('utf8'))
capture('accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; only Chapter2 required unbounded OSD failure proof package accepted','--leaf',TASK,'--kind','review','--statement',bound,'--file',final,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:unbounded-OSD-FINAL:accepted','--trials',RUN/'trials.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
_,out=capture('accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
for p in [native[0],native[1]]:assert p.read_bytes().startswith(before[p] or b'')
ts=native[0].read_bytes()[len(before[native[0]] or b''):].decode('utf8').splitlines();assert len(ts)==1
tr=json.loads(ts[0]);assert (tr['task'],tr['role'],tr['kind'],tr['status'])==(TASK,'reviewer','review','accepted')
assert tr['new_declarations']==names and tr['notes']==notes and tr['reviewer_validated'] is True
assert (tr['obligations_before'],tr['obligations_after'])==(11,0) and tr['verifier_evidence']==[str(final)]
es=native[1].read_bytes()[len(before[native[1]]):].decode('utf8').splitlines();assert len(es)==1
ev=json.loads(es[0]);state=json.loads(before[native[2]])
assert ev['session_id']==TASK and ev['event_type']=='accepted' and ev['payload']==payload
assert ev['sequence']==state['next_sequence'] and ev['parent_id']==state['current_entry_id']
expected=copy.deepcopy(state);expected.update(next_sequence=state['next_sequence']+1,current_entry_id=ev['entry_id'])
assert load(native[2])==expected and native[3].read_bytes()==before[native[3]]
reset=copy.deepcopy(c)
for a,b in allowed:reset[a][b]=oldc[a][b]
assert reset==oldc
for p in docs:assert p.read_bytes()==before[p]+suffix.encode('utf8')
changes=[]
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:
    p=Path(row['path'])
    if sha(p)!=row['sha256']:
        assert p in before and before[p] is not None and hashlib.sha256(before[p]).hexdigest()==row['sha256'],p
        changes.append(dict(path=p.as_posix(),before_sha256=row['sha256'],after_sha256=sha(p)))
write(RUN/'post-native-root-audit-v1.json',dict(scope=bound,trial=tr,event=ev,state_exact_expected=True,own_journal_unchanged=True,contribution_fields=allowed,docs_suffix=suffix,changed_FINAL_inputs=changes,all_other_FINAL_inputs_unchanged=True,created_trial=before[native[0]] is None,shadow=shadow,root_self_audit_only=True,distinct_post_native_review='pending',chapter_complete=False,whole_Goal='ACTIVE'))
fixed()
print('Own native bounded acceptance and exact metadata transitions audited; distinct postnative review pending.',flush=True)
