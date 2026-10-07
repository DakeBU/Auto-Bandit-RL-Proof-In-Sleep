"""Bounded actual example acceptance only, after real gates and distinct FINAL."""
from common_v4 import *
f=fixed(True,True);integrated=load(RUN/'integrated-gates-overlay-v1.json')
for label in integrated['actual_passed_gates']:passed(label)
history=load(RUN/'history-binding-audit-v2.json');snap={(str(Path(r['path']).resolve()),r['raw_sha256']):r['resolved_raw_file'] for r in history['rows']}
for row in load(RUN/'historical-raw-supersession-final-v1.json')['rows']:
 assert sha(row['snapshot'])==row['raw_sha256'];snap[(str(Path(row['path']).resolve()),row['raw_sha256'])]=row['snapshot']
final=load(RUN/'final-reader-receipt-v1.json');assert final['actor']['task']=='/root/source_reviewer' and final['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not final.get('required_reader_corrections',[]) and not final.get('required_blocking_reader_repairs',[])
assert set(final['reader_requirement_verdicts'])=={'R'+str(i) for i in range(1,9)}
assert all(r['verdict']=='satisfied' for r in final['reader_requirement_verdicts'].values())
rejected=load(RUN/'source-contract-receipt-v1.json');assert rejected['verdict']=='rejected'
contract=load(RUN/'source-contract-receipt-v2.json');assert contract['repair_verdict']['M1']['verdict']=='satisfied'
append_paths={str(Path(p).resolve()) for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']};rows=[];discharges=[];cache={}
def h(p):
 p=str(Path(p).resolve())
 if p not in cache:cache[p]=sha(p)
 return cache[p]
for receipt in ['source-contract-receipt-v2.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
 r=load(RUN/receipt);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'];assert h(r['report'])==r['report_sha256']
 for key in ['required_repairs','required_mathematical_repairs','mathematical_repairs','required_metadata_repairs']:assert not r.get(key,[]),(key,r.get(key))
 if receipt!='final-reader-receipt-v1.json':
  required=r['required_reader_corrections'];assert len(required)==8 and {s.split(':',1)[0] for s in required}==set(final['reader_requirement_verdicts'])
  discharges.append(dict(original_receipt=receipt,original_receipt_sha256=h(RUN/receipt),original_reader_requirements=required,discharged_by='final-reader-receipt-v1.json',final_receipt_sha256=h(RUN/'final-reader-receipt-v1.json'),final_verdicts=final['reader_requirement_verdicts'],original_receipt_unmodified=True))
 reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
 if receipt=='final-reader-receipt-v1.json':
  for row in load(RUN/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
 for p,d in reviewed.items():
  resolved=p if h(p)==d and str(Path(p).resolve()) not in append_paths else snap[(str(Path(p).resolve()),d)];assert h(resolved)==d,p;rows.append(dict(receipt=receipt,path=p,sha256=d,resolved=resolved))
write(RUN/'accepted-reader-discharge-v1.json',dict(status='passed',rows=discharges,all_eight_original_reader_obligations_explicitly_satisfied=True,rejected_contract_v1_preserved=True,metadata_M1_separately_repaired_v2=True,original_receipts_reports_unchanged=True,mathematical_repairs=[]))
boundary=dict(source_package_accepted=True,chapter_complete=False,goal_complete=False)
b=load(RUN/'public-actual-bindings-v1.json');g=load(RUN/'compiled-dependencies-v1.json')
counts=dict(source_formal_results=1,source_definitions=1,retained_public_proofs=0,retained_definitions=0,new_public_proofs=3,new_definitions=1,new_test_proofs=5,whole_canary_proofs=5,whole_canary_definitions=0,whole_canary_abbreviations=0,named_kernel_checks=9,native_guards=4,selected_graph_nodes=9,selected_graph_direct_references=g['direct_references'],actual_required_value_pairs=len(g['required_value_pairs']),focused_jobs=b['focused_jobs'],root_Tests_jobs=integrated['root_Tests_jobs'],full_tests=integrated['full_tests'],existing_skips=integrated['existing_skips'],canonical_public_nodes=4,highlight_links=3,curated_links=3,notation_entries=4,source_cards=3,old_registry_IDs_URLs_preserved=10811,new_registry_nodes=4,total_registry_nodes=integrated['total_registry_nodes'])
manifest='research-wiki/contribution-contracts/online-convex-nondifferentiability-20261007.json';delta=load(manifest)['truth_boundary']
scope='Orabona v10 ONE unnumbered real2 convex example afterT2.30/end2.2.1 before2.2.2 printed19/PDF31: actual global convexity plus ALL CLOSED-segment AMBIENT nondifferentiability; stronger all-axis library leaf explicit; cardinality separate REQUIRED'
write(RUN/'accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(rows),rows=rows,all_final_fixed_inputs_rechecked=True,frozen_headers=f['headers'],raw_definition_headers_unchanged=True,prior_accepted_rejected_reports_receipts_preserved=True,native_resolution_immutable_reviewed_snapshots=True))
write(RUN/'accepted-decision-v1.json',dict(status=final['verdict'],scope=scope,frozen_headers=f['headers'],explicit_delta=delta,qualified_public_module_sha256=sha(PUBLIC),site_source_commit=integrated['site_source_commit'],stacked_base=BASE,stacked_base_PR=176,final_review_report_sha256=final['report_sha256'],mathematical_repairs=[],nonmathematical_repairs=integrated['failure_repairs'],main_relative_gate=integrated['main_relative_gate'],native_fence_limit=integrated['native_fence_limit'],cached_jobs_included=True,full_registry_graph_export=False,formal_uncountability_required_separate=True,chapter_mandatory_total=None,PR_delivery_pending=True,legacy_queue=0,legacy_zero_not_chapter_completion=True,merged=False,live=False,**counts,**boundary))
remaining='Formal uncountability consequence/Lemma2.31/OSD/linearization/Example2.32/unitanalysis/remainingChapter1/2maintext/nineOTHERChapter1 main-relative contract gaps/necessaryappendices REQUIRED. Chapter2totalnull/incomplete/legacyqueue0notcompletion;3-16unenumerated,totalGoalACTIVE.'
write(RUN/'accepted-obligations-v1.json',dict(required=[dict(name=PRE+n,statement_hash=d,state='accepted exact unnumbered example only') for n,d in f['headers'].items()],chapter2_total=None,next_required=remaining,**counts,**boundary))
write(RUN/'source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),additive_only=True,source_anchor=scope,accepted_public_names=[PRE+n for n in f['headers']],formal_uncountability_required_separate=True,**counts,**boundary))
write(RUN/'contribution-acceptance-overlay-v1.json',dict(manifest=manifest,manifest_sha256=sha(manifest),effective_source_contract='source-contract-receipt-v2.json',rejected_source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',integrated='integrated-gates-overlay-v1.json',accepted_decision='accepted-decision-v1.json',earlier_candidate_pending_fields_superseded_additively=True,**boundary))
digest=TASK+' '+scope+'. Required distinct automated formalizer/neutraldecoder/source reviewer requestedAstra medium; no human/external/runtimeattestation. Same frozen mathematical statements; actual source metadata/API/native-schema/harness-index failures retained/repaired. All R1-R8 discharged by actual FINAL, original receipts unchanged. '+remaining+' No merge/deploy/mainlive/retirement.'
write(RUN/'memory-digest-accepted-v1.md',digest);write(RUN/'retrieval-index-accepted-v1.md',digest+' Actual9types9kernel4guards/selected9nodes1194refs9actualpairs, shared10815nodes with10811oldIDsURLs unchanged; not declaration-count productivity.')
write(RUN/'program-milestone-v1.json',dict(total_Goal='Chapters1-16 ACTIVE unbudgeted',bounded_milestone=scope,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,chapters3_16='unenumerated mandatory',main_updated=False,live_updated=False,**counts,**boundary))
native('accepted-reviewer-trial-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','NONDIFF-BODY-V2','--statement-hash',f['headers']['convex_nondifferentiable_segment'],'--reused-declaration',PRE+'convex_nondifferentiable_segment','--verifier-evidence',RUN/'final-reader-receipt-v1.json','--harness','hierarchical','--progress-class','compiled-leaf','--reviewer-validated','--notes','Actual globalconvex/ambient closedsegment producer terminal accepted after real combined gates and distinct FINAL. Three new public proofs/one definition/five actual2D canaries; cardinality separate REQUIRED. No chapter/book/productivity claim.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()];write(RUN/'accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==TASK))
event('accepted',dict(accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),new_proofs=3,new_definitions=1,merged=False,live=False,**boundary))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('accepted-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; exact2D unnumberedexample accepted only, cardinality/chapter/book REQUIRED','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'convex_nondifferentiable_segment'),'--declaration',PRE+'convex_nondifferentiable_segment','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+PRE+'coordinate_absolute_convex:compiled','--dependency','lean:'+PRE+'coordinate_absolute_not_differentiable:compiled','--dependency','review:source-reader:accepted','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
fixed(True,True);write(RUN/'native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision_sha256=sha(RUN/'accepted-decision-v1.json'),actual_attempt='NONDIFF-BODY-V2',globalSGB_unchanged=True,PR_delivery_pending=True,**boundary))
print('Only exact unnumbered2D source example accepted; formal cardinality/real PR remaining/GoalACTIVE.')
