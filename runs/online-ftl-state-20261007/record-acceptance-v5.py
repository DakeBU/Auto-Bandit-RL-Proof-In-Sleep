from common_v1 import *
fixed(proving=True,integrated=True)
final=load(RUN/'final-reader-receipt-v1.json');body=load(RUN/'body-bindings-v1.json');i=load(RUN/'integrated-gates-overlay-v1.json')
assert final['actor']['task']=='/root/source_reviewer' and final['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(final['report'])==final['report_sha256']
requirements=load(RUN/'source-contract-receipt-v1.json')['required_reader_corrections']
assert set(final['reader_requirement_verdicts'])=={'R'+str(n) for n in range(1,9)}
for row in requirements:
 v=final['reader_requirement_verdicts'][row['id']];assert v['verdict']=='satisfied' and v['requirement']==row['requirement']
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs','required_blocking_reader_repairs']:assert not final.get(key,[]),key
audits=[]

resolution=load(RUN/'catalog-scope-reviewed-source-resolution-v6.json')
scope_receipt=load(RUN/'catalog-scope-receipt-v6.json');assert scope_receipt['verdict']=='accepted-with-explicit-delta' and sha(scope_receipt['report'])==scope_receipt['report_sha256']
scope_reviewed={x['path']:x['sha256'] for x in scope_receipt['reviewed_files']}
for x in load(RUN/'catalog-scope-review-inputs-v6.json')['rows']:
 p=x['path'];resolved=resolution['immutable_snapshot'] if Path(p).resolve()==(ROOT/resolution['original_live_path']).resolve() else p
 assert scope_reviewed[p]==x['sha256']==sha(resolved),p
for p,h in scope_reviewed.items():
 resolved=resolution['immutable_snapshot'] if Path(p).resolve()==(ROOT/resolution['original_live_path']).resolve() else p
 assert sha(resolved)==h,p

for receipt,inputs in [('source-contract-receipt-v1.json','source-contract-inputs-v1.json'),('public-body-receipt-v1.json','body-review-inputs-v1.json'),('final-reader-receipt-v1.json','final-reader-inputs-v1.json')]:
 r=load(RUN/receipt);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
 reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
 for x in load(RUN/inputs)['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
 for p,h in reviewed.items():assert sha(p)==h,p
 audits.append(dict(receipt=receipt,receipt_sha256=sha(RUN/receipt),report_sha256=r['report_sha256'],fixed_rows=len(load(RUN/inputs)['rows']),all_raw_bindings_match=True))
audits.append(dict(receipt='catalog-scope-receipt-v6.json',receipt_sha256=sha(RUN/'catalog-scope-receipt-v6.json'),report_sha256=scope_receipt['report_sha256'],fixed_rows=19,all_raw_bindings_match=True,reviewed_scanner_resolution=resolution))
assert requirements==load(RUN/'public-body-receipt-v1.json')['required_reader_corrections']
for label in i['actual_passed_gates']:assert load(RUN/(label+'-exit.json'))['exit_code']==0,label
scope='Nine new public proofs and three definitions close two required source subobligations: arbitrary feasible initial prediction and actual recursive exact-real mean/count state. Four old Mean proofs retained; every old FTL declaration retained. Six validation proofs are not six book results.'
remaining='Chapter1 W/V action-domain mapping, logarithmic lower-bound/source-claim audit and actual chapter reconciliation remain required. Source inventory16 maintext items; mandatory proof totalnull. Actual main-relative gate resolves Mean, seven other gaps Asymptotic/Foundations/History/IID/Information/Regret/Stochastic FAILUNWAIVED. Chapter2null/incomplete,3–16unenumerated,necessaryappendicesrequired,wholeGoalACTIVE. No merge/main/live/retirement.'
boundary=dict(source_package_accepted=True,chapter_complete=False,goal_complete=False,merged=False,live=False,new_public_math=9,new_public_definitions=3,new_source_subobligation_closures=2,new_production_registry_nodes=12,new_named_validation_proofs=6)
write(RUN/'accepted-binding-audit-v1.json',dict(status='passed',reviews=audits,all_prior_raw_bindings_unchanged=True))
write(RUN/'accepted-reader-discharge-v1.json',dict(status='passed',original_requirements=requirements,actual_FINAL_verdicts=final['reader_requirement_verdicts'],all_R1_R8_satisfied=True))
write(RUN/'accepted-decision-v1.json',dict(status=final['verdict'],scope=scope,contract_version=1,Mean_sha256=sha(MEAN),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),native_statement_hashes={x['name']:x['statement_hash'] for x in load(RUN/'full-fence-bindings-v1.json')},BODY=body,BODY_review_current=dict(status="accepted-with-explicit-delta",receipt_sha256=sha(RUN/"public-body-receipt-v1.json"),historical_pending_field_retained=True),source_presentation_repair=dict(scope_receipt_sha256=sha(RUN/"catalog-scope-receipt-v6.json"),implementation_sha256=sha(RUN/"catalog-implementation-bindings-v7.json"),registry_repair_sha256=sha(RUN/"registry-boundary-repair-v5.json"),new_python_regression_tests=6),applicable_integrated_gates=i,final_report_sha256=final['report_sha256'],exact_base_PR=188,exact_base_head=BASE,remaining_required=remaining,PR_delivery_pending=True,**boundary))
write(RUN/'accepted-obligations-v1.json',dict(public_terminals=[PRE+n for n in load(CONTRACT/'new-public-headers-v1.json')],public_terminal_status='Actual all-time recursive producer and generalinitial properties closed',named_validation_targets=[TEST+n for n in load(CONTRACT/'planned-canary-headers-v1.json')],remaining_required=remaining,**boundary))
write(RUN/'program-milestone-v1.json',dict(total_Goal='Chapters1–16 ACTIVE/unbudgeted',bounded_scope=scope,chapter1_source_items=16,chapter1_mandatory_total=None,chapter1_main_relative_contributor_gaps=load(RUN/'main-relative-diagnostic-v1.json')['actual_production_gaps'],chapter2_mandatory_total=None,chapters3_16='unenumerated mandatory',necessary_appendices='required',main_updated=False,live_updated=False,**boundary))
digest=TASK+' '+scope+' '+remaining+' Source arbitraryinitial printed3/PDF15, running-summary printed6/PDF18, half-onlyquarter printed4–5/PDF16–17. Actual24kernel/19exacttypeidentities/19fulltheoremfences/16VALUE1979refs. Exact-real noncomputable count/value, no fixed-bit/runtime certificate. Same fixed c/strictprefix/currentlabel afterprediction; firststepcancelsc; allreal algebraic versus intervalfeasibility; six actual canaries including changing means/currentperturbation/halfregret/outside2/feasible1notquarter. All preparation/guard/recursive-rfl/layout/no-goal/digest-version failures and repairs retained, no source weakening. Distinct required automated actors reusedhistory/requestedAstra-medium/nohumanexternalruntimeattestation.'
write(RUN/'memory-digest-accepted-v1.md',digest);write(RUN/'retrieval-index-accepted-v1.md',digest)
write(RUN/'source-inventory-acceptance-overlay-v1.json',dict(old_inventory='docs/contracts/online-book-v1/source-inventory.json',old_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),old_inventory_unchanged=True,source_mappings=[dict(source_subobligation='C1-FTL-GENERAL-INITIALIZATION',lean_name=PRE+'ftlPredict_mem',printed=3,pdf=15),dict(source_subobligation='C1-FTL-STREAMING-STATE',lean_name=PRE+'ftlState_eq_predict',printed=6,pdf=18)],new_inventory_items_added=0,chapter_ledger=(CONTRACT/'chapter-one-source-ledger-draft-v1.json').as_posix(),remaining_required=remaining,**boundary))
statement=load(RUN/'native-public-fences/ftlState_eq_predict-v1.json')
native('accepted-reviewer-trial-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','FTL-STATE-BODIES-V1','--statement-hash',statement['statement_hash'],*[z for n in load(CONTRACT/'new-public-headers-v1.json') for z in ['--new-declaration',PRE+n]],'--verifier-evidence',RUN/'final-reader-receipt-v1.json','--harness','hierarchical','--progress-class','closed-frontier','--reviewer-validated','--notes',digest)
own=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip() and json.loads(s).get('task')==TASK]
assert sum(t.get('status')=='accepted' and t.get('role')=='reviewer' for t in own)==1
write(RUN/'accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(x) for x in own))
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),**boundary)))
native('accepted-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1–16; two causal FTL state obligations accepted','--leaf',TASK,'--kind','lean','--statement',statement['statement'],'--declaration',PRE+'ftlState_eq_predict','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+PRE+'empiricalMean_succ:compiled','--dependency','review:source-reader:accepted','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads((RUN/'accepted-frontier-shadow-v1.log').read_text(encoding='utf-8'));assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','verified_lemma','--task',TASK,'--provenance-kind','source-reviewed-new-proof-package','--provenance',RUN/'accepted-decision-v1.json','--declaration',PRE+'ftlState_eq_predict','--file',PUBLIC,'--status','verified','--verifier',RUN/'final-reader-receipt-v1.json','--role','reviewer','--details-json',json.dumps(dict(scope=scope,remaining_required=remaining,**boundary)),'--output',RUN/'accepted-memory-record-v1.json')
native('accepted-retrieval-record-v1','retrieval-record','--task',TASK,'--query','Generalinitial causal FTL real mean count local transition alltime state identity','--candidate',PRE+'empiricalMean_succ','--candidate',PRE+'ftlState_eq_predict','--compiled-scratch',RUN/'leaves/all-exact-types-v2.lean','--provenance',RUN/'all-exact-types-v2-exit.json','--output',RUN/'accepted-retrieval-record-v1.json')
write(RUN/'native-acceptance-overlay-v1.json',dict(status='passed',one_accepted_reviewer_trial=True,all_failures_retained=True,globalSGB_unchanged=True,PR_delivery_pending=True,**boundary))
fixed(proving=True,integrated=True)
