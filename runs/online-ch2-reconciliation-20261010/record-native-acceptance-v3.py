from publication_guard_v5 import *
import copy
fixed()
final=RUN/'FINAL-review-v1.json';review=load(final)
assert review['package_verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']
assert sha(review['report'])==review['report_sha256'] and sha(RUN/'FINAL-inputs-v1.json')==review['input_manifest_sha256']
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
headers=load(LEAF/'frozen-headers-draft-v1.json')['rows'];names=[r['declaration'] for r in headers]
assert len(names)==9 and sha(RUN/'record-native-acceptance-v3.py')==review['approved_native_helper_sha256']
docs=[ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
native=[RUN/n for n in ['trials.jsonl','lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
attrs=RUN/'.gitattributes'
mutable=[CONTRIBUTION,attrs,*docs,*native];before={p:p.read_bytes() if p.exists() else None for p in mutable}
assert before[native[0]] is None
write(RUN/'pre-native-exact-bytes-v1.json',dict(FINAL_sha256=sha(final),rows=[dict(path=p.as_posix(),exists=raw is not None,sha256=hashlib.sha256(raw).hexdigest() if raw is not None else None,before_raw_base64=base64.b64encode(raw).decode('ascii') if raw is not None else None) for p,raw in before.items()]))
ap=load(RUN/'native-attribute-plan-v1.json')
assert sha(attrs)==ap['before_sha256'] and sha(ap['after_snapshot'])==ap['after_sha256']
attrs.write_bytes(Path(ap['after_snapshot']).read_bytes())
bound=load(RUN/'accepted-boundary-proposal-v1.json')['boundary']
reg=load(RUN/'registry-inspected-v1.json')
write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nNine frozen production proof terminals, four definitions and eight FULL public canaries accepted only as one generic FTL definition foundation with bounded qualified provenance reconciliation. Distinct FINAL '+sha(final)+'. Actual harness '+sha(RUN/'full-harness-inspected-v2.json')+'; clean local SITE source '+reg['source_commit']+' preserves11041completeoldobjects+13canonicalproduction=11054.28actualdesktoporiginals root+distinctFINAL, localfile notHTTP/live/mobile. Native9->0 ONLY9frozenproductionproofterminals; postnative/delivery pending.\n')
notes=bound+' Distinct source_reviewer FINAL '+sha(final)+'. Native9->0 ONLY9frozenproductionproofterminals; postnative/delivery pending.'
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','nine-frozen-generic-FTL-proofs-v1','--progress-class','closed-frontier','--reviewer-validated','--obligations-before','9','--obligations-after','0','--notes',notes,'--verifier-evidence',final]
for n in names:args+=['--new-declaration',n]
capture('native-acceptance-trial-v1',*args)
payload=dict(scope=bound,terminals=[dict(declaration=r['declaration'],statement_hash=lifecycle.statement_hash(r['exact_header'])) for r in headers],source_definitions=4,full_canaries=8,FINAL_sha256=sha(final),recorded_by='/root from distinct /root/source_reviewer decision',bounded_obligations_before=9,bounded_obligations_after=0,source_family_count=1,source_container_closed=False,chapter_proof_total=None,chapter_complete=False,goal_complete=False,post_native_review='pending',delivery='pending')
event('native-acceptance-event-v1','accepted',payload)
c=load(CONTRIBUTION);oldc=copy.deepcopy(c)
allowed=[('semantic_roundtrip','remaining_semantic_delta'),('verification','independent_review'),('graph_contribution','visual_review'),('verification','site_check')]
c['semantic_roundtrip']['remaining_semantic_delta']=bound+' Distinct staged decoder/CONTRACT/productionBODY/canaryBODY/integration/helper/FINAL '+sha(final)+'. Related automated actor history disclosed, no human/external/absolute-blind/runtime attestation. OWN postnative/delivery pending.'
c['verification']['independent_review']='Distinct bounded FINAL '+sha(final)+' accepts9frozenproductionproofterminals/4definitions/8FULLcanaries, exact qualified provenance repair, actual combined gates, shared registry and28originaldesktop pixels. Not13printedresults or chapter closure. Postnative/delivery pending.'
c['graph_contribution']['visual_review']='24selectedcompiledvalues(13production/8publicTest/3privateTesthelpers);11individually selectedconjunct audits. DirectTYPE/VALUEpresences only, notfulltransitive, proofnecessity, exclusivity or source-resultcount.11041completeoldregistryobjects+13canonicalproduction=11054;14sourcecards. Actuallocalfiledesktop1440/17sourceguideMathJaxformulas/zeroerrors/foldedLean/builtinwrap/28originals root+distinctFINAL. NoTest/perBookduplicate/HTTP/live/allviewport claim.'
c['verification']['site_check']='Actualsitecheck, complete11041oldregistryobjectsunchanged+13canonicalproduction=11054;14cards.17sourceguideMathJaxformulas/zeroerrors/foldedLean/wrap and28originaldesktop images personallyviewedbyroot+distinctFINAL '+sha(final)+'. Cleansitecandidate source '+reg['source_commit']+', notfreshatlater evidenceHEAD. Local-only; postnative/delivery pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nBounded package FINAL accepted: '+bound+' FINAL SHA '+sha(final)+'. OWN native9->0 ONLY9frozenproductionproofterminals;4definitions/8canaries separately tracked. Postnative/draftPR pending. Earlier gate-pending text is historical.\n'
for p in docs:p.write_bytes(before[p]+suffix.encode('utf8'))
# Native output is retained under ignored tmp with exact RAW base64; the OWN JSON copy is explicitly derived LF serialization.
output=ROOT/'tmp'/(TASK+'-accepted-frontier-v1.json');assert not output.exists()
capture('accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; only bounded generic FTL definition foundation and qualified reconciliation accepted','--leaf',TASK,'--kind','review','--statement',bound,'--file',final,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:generic-FTL-FINAL:accepted','--trials',RUN/'trials.jsonl','--output',output,'--shadow-status','pending')
write(RUN/'accepted-frontier-native-output-raw-v1.json',dict(path=output.as_posix(),sha256=sha(output),raw_base64=base64.b64encode(output.read_bytes()).decode('ascii'),derived_copy=(RUN/'accepted-frontier-v1.json').as_posix(),scope='Exact native CRLF output retained; OWN copy is explicit parsed LF serialization, not an unchanged-byte claim.'))
write(RUN/'accepted-frontier-v1.json',load(output))
_,out=capture('accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
for p in [native[0],native[1]]:assert p.read_bytes().startswith(before[p] or b'')
ts=native[0].read_bytes()[len(before[native[0]] or b''):].decode('utf8').splitlines();assert len(ts)==1
tr=json.loads(ts[0]);assert (tr['task'],tr['role'],tr['kind'],tr['status'])==(TASK,'reviewer','review','accepted')
assert tr['new_declarations']==names and tr['notes']==notes and tr['reviewer_validated'] is True
assert (tr['obligations_before'],tr['obligations_after'])==(9,0) and tr['verifier_evidence']==[str(final)]
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
write(RUN/'post-native-root-audit-v1.json',dict(FINAL_sha256=sha(final),contribution_after_sha256=sha(CONTRIBUTION),scope=bound,trial=tr,event=ev,state_exact_expected=True,own_journal_unchanged=True,contribution_fields=allowed,docs_suffix=suffix,changed_FINAL_inputs=changes,all_other_FINAL_inputs_unchanged=True,created_trial=True,shadow=shadow,root_self_audit_only=True,distinct_post_native_review='pending',chapter_complete=False,whole_Goal='active'))
assert sha(attrs)==ap['after_sha256']
fixed()
print('Bounded OWN native9->0 and exact metadata transitions audited; distinct postnative/delivery pending.',flush=True)
