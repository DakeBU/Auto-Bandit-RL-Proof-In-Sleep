from common_v1 import *
fixed(integrated=True)
requirements=load(RUN/'source-contract-receipt-v1.json')['required_reader_corrections']
final=load(RUN/'final-reader-receipt-v1.json');resolution=load(RUN/'body-reviewed-source-resolution-v1.json')
assert final['actor']['task']=='/root/source_reviewer' and final['verdict'] in ['accepted','accepted-with-explicit-delta']
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs','required_blocking_reader_repairs']:assert not final.get(key,[]),key
assert set(final['reader_requirement_verdicts'])=={'R'+str(n) for n in range(1,9)}
for row in requirements:
 v=final['reader_requirement_verdicts'][row['id']];assert v['verdict']=='satisfied' and v['requirement']==row['requirement']
assert requirements==load(RUN/'public-body-receipt-v1.json')['required_reader_corrections']
audits=[]
for receipt,inputs in [('source-contract-receipt-v1.json','source-contract-inputs-v1.json'),('public-body-receipt-v1.json','body-review-inputs-v1.json'),('final-reader-receipt-v1.json','final-reader-inputs-v1.json')]:
 r=load(RUN/receipt);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
 reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
 for row in load(RUN/inputs)['rows']:
  p=row['path'];resolved=resolution['immutable_snapshot'] if receipt=='public-body-receipt-v1.json' and Path(p).resolve()==PUBLIC.resolve() else p
  assert reviewed[p]==row['sha256']==sha(resolved),p
 for p,h in reviewed.items():
  resolved=resolution['immutable_snapshot'] if receipt=='public-body-receipt-v1.json' and Path(p).resolve()==PUBLIC.resolve() else p
  assert sha(resolved)==h,p
 audits.append(dict(receipt=receipt,receipt_sha256=sha(RUN/receipt),fixed_rows=len(load(RUN/inputs)['rows']),all_raw_bindings_match=True))
for label in ['combined-root-v1','combined-Tests-v1','full-harness-v2','contributor-exact-base-v3','site-build-v1','site-check-v1','registry-check-v4','current-reader-capture-v4']:assert load(RUN/(label+'-exit.json'))['exit_code']==0,label
i=load(RUN/'integrated-gates-v3.json');r=load(RUN/'registry-v4.json');p=load(RUN/'pixel-review-v1.json')
assert i['committed_production_paths']==4 and i['committed_manifests']==1 and r['new_registry_nodes']==0 and r['status']==p['status']=='passed'
assert r['preserved_base_node_IDs_URLs_and_hashes']==10835 and not r['source_dirty'] and r['lean_verified']
scope='One required typed W/V loss-domain/comparator model mapping audited with actual shared Regret API. Existing two public proofs/two definitions reused; zero new production mathematics/definitions/registry nodes. Eight validation proofs/eight fixture definitions are tests.'
remaining='Full C1 regret/minimum and no-regret reconciliation, logarithmic lower-bound/source claim and other mandatory module audits remain required. Inventory16 source items/mandatory proof totalnull. Six OTHER main-relative contributor gaps FAILUNWAIVED. Chapter2incomplete/null;3–16unenumerated/necessaryappendicesrequired/totalGoalACTIVE. ExactOPENunmergedPR189stack; no main/live/merge/deploy/retirement.'
boundary=dict(source_package_accepted=True,chapter_complete=False,goal_complete=False,merged=False,live=False,new_public_math=0,new_public_definitions=0,new_source_subobligation_closures=1,new_production_registry_nodes=0,new_named_validation_proofs=8)
write(RUN/'accepted-binding-audit-v1.json',dict(status='passed',reviews=audits,original_BODY_source_resolution=resolution,all_prior_raw_binding_bytes_preserved=True))
write(RUN/'accepted-reader-discharge-v1.json',dict(status='passed',original_requirements=requirements,actual_FINAL_verdicts=final['reader_requirement_verdicts']))
write(RUN/'accepted-decision-v1.json',dict(status=final['verdict'],scope=scope,remaining_required=remaining,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),contract_version=1,body_bindings=load(RUN/'body-bindings-v1.json'),applicable_integrated=i,registry_record_sha256=sha(RUN/'registry-v4.json'),applicable_site_commit=r['source_commit'],pixel_record_sha256=sha(RUN/'pixel-review-v1.json'),final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),exact_base_PR=189,exact_base_head=BASE,PR_delivery_pending=True,**boundary))
write(RUN/'source-inventory-acceptance-overlay-v1.json',dict(old_inventory='docs/contracts/online-book-v1/source-inventory.json',old_inventory_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),old_inventory_unchanged=True,source_subobligation='C1-REGRET-DIFFERENT-ACTION-COMPARATOR-SETS',printed_page=2,pdf_page=14,source_scope='Footnote1 modelling possibility; no generic algorithm guarantee',reused_public=[PRE+n for n in ['comparatorRegret','NoRegret','comparatorRegret_eq_sum','noRegret_of_vanishing_bound']],chapter_ledger=(CONTRACT/'chapter-one-source-ledger-draft-v1.json').as_posix(),full_C1_Regret_and_NoRegret_open=True,remaining_required=remaining,**boundary))
digest=TASK+' '+scope+' '+remaining+' Distinct required reused automated roles/history disclosed/requestedAstra-medium/no external human or runtime attestation. Actual20kernel10Props10definitionidentities10fullnativeguards3VALUEpairs/root9093Tests9245/harness472skip7. Source arbitrary-carrier/ordinarylimit versus eventualepsilon interpretation explicit. Supplied sameprediction, no causal producer/minimumexistence; concrete negativegame loss/output derivedbound0. Same10835registryIDsURLs/hashesequal,8currentpanels root-viewed. Retained untrackedcanary,index-orderN/A,manifestcase,verifierUI/raw-copy failures repaired without target weakening.'
write(RUN/'memory-digest-accepted-v1.md',digest);write(RUN/'retrieval-index-accepted-v1.md',digest)
statement=load(RUN/'full-header-fences-v1/domain_gap_sum.json')
native('accepted-reviewer-trial-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','REGRET-DOMAINS-BODIES-V1','--statement-hash',statement['statement_hash'],'--reused-declaration',PRE+'comparatorRegret_eq_sum','--reused-declaration',PRE+'noRegret_of_vanishing_bound','--verifier-evidence',RUN/'final-reader-receipt-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reviewer-validated','--notes',digest)
own=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip() and json.loads(s).get('task')==TASK]
assert sum(x.get('status')=='accepted' and x.get('role')=='reviewer' for x in own)==1
write(RUN/'accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(x,ensure_ascii=False) for x in own))
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),**boundary)))
native('accepted-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1–16; typed W/V model subobligation accepted','--leaf',TASK,'--kind','lean','--statement',statement['statement'],'--declaration',TEST+'domain_gap_sum','--file',CANARY,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+PRE+'comparatorRegret_eq_sum:compiled','--dependency','lean:'+PRE+'noRegret_of_vanishing_bound:compiled','--dependency','review:source-reader:accepted','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads((RUN/'accepted-frontier-shadow-v1.log').read_text(encoding='utf-8'));assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','checkpoint','--task',TASK,'--provenance-kind','source-reviewed-shared-API-model-mapping','--provenance',RUN/'accepted-decision-v1.json','--declaration',PRE+'comparatorRegret_eq_sum','--file',PUBLIC,'--status','accepted','--verifier',RUN/'final-reader-receipt-v1.json','--role','reviewer','--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),'--output',RUN/'accepted-memory-record-v1.json')
native('accepted-retrieval-record-v1','retrieval-record','--task',TASK,'--query','Typed W-loss W-output V comparator embedding and per-comparator eventual upper no-regret','--candidate',PRE+'comparatorRegret_eq_sum','--candidate',PRE+'noRegret_of_vanishing_bound','--compiled-scratch',CANARY,'--provenance',RUN/'all-canary-bodies-v1-exit.json','--output',RUN/'accepted-retrieval-record-v1.json')
write(RUN/'native-acceptance-overlay-v1.json',dict(status='passed',one_accepted_reviewer_trial=True,progress_class='retrieval-reuse',no_new_verified_lemma_record=True,globalSGB_unchanged=True,PR_delivery_pending=True,**boundary))
for folder in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']:
 path=Path(folder)/(TASK+'.md');path.write_bytes(path.read_bytes()+('\n\n## Actual bounded mapping accepted; delivery pending\n\n'+digest+'\n').encode('utf-8'))
fixed(integrated=True)
