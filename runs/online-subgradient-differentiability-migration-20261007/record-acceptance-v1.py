"""Accept only the exact T2.22 source package after distinct FINAL and actual gates."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));cache={}
def sha(p):
 k=str(p)
 if k not in cache:cache[k]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[k]
def write(n,x):
 p=run/n;assert not p.exists(),p
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
history=load(run/'history-binding-audit-v1.json')
snapshots={(r['path'],r['raw_sha256']):r['resolved_raw_file'] for r in history['rows']}
rows=[];final=None
for n in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
 r=load(run/n);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
 assert not r.get('mathematical_repairs',[]) and not r.get('required_repairs',[]) and sha(r['report'])==r['report_sha256']
 reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
 if n=='final-reader-receipt-v1.json':
  final=r
  for row in load(run/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
 for p,h in reviewed.items():
  resolved=p if sha(p)==h else snapshots[(p,h)];assert sha(resolved)==h,p
  rows.append(dict(receipt=n,path=p,sha256=h,resolved=resolved))
integrated=load(run/'integrated-gates-overlay-v1.json')
for label in integrated['actual_passed_gates']:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean')
assert public.read_bytes().endswith((run/'original-OnlineSubgradientDifferentiability.lean.txt').read_bytes())
assert sha(public)==load(run/'public-comment-qualification-v1.json')['qualified_sha256']==load(run/'integrated-public-guard-audit-v2.json')['public_module_sha256']
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for group in ['fixed_shared_files','whole_old_canary']:
 for p,h in freeze[group].items():assert sha(p)==h,p
assert Path('Tests.lean').read_bytes().startswith((run/'original-Tests.lean.txt').read_bytes())
assert sha('Tests/OnlineDifferentiabilityBoundaryCanary.lean')==load(run/'public-actual-bindings-v1.json')['new_canary_sha256']
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
boundary=dict(source_package_accepted=True,chapter_complete=False,goal_complete=False)
delta='One printed Theorem2.22 full iff AND every-real-representative gradient identity. Genuine finite real AMBIENT differentiable germ, not mere toReal/relative-domain derivative. Main only convex REAL-height epigraph and finite point; both directions derive noBottom/properness/interior. Eleven proofs finiteD realinner with completeness derived/dimension0 permitted, definition noFD. Global supports all ambient queries including topoutside; helper noBottom/NeBot/positiveball/Lipschitz/continuity assumptions not main assumptions. Reverse actual original-domain nonzero normal contradiction/local support bounds/nontrivial limits/compact unique cluster/selected supports/two actual inequalities/littleO; forward actual contact/Theorem2.7/localminimum derivativezero/Riesz injectivity/eventual representative gradient equality. Internal proof choice not algorithm/measurable oracle. Adjacent introductory sentence under convex scope. Real singleton diagnostics do not assert dimension0emptyinterior.'
counts=dict(source_numbered_anchors=1,source_unnumbered_required_results=0,retained_public_proofs=11,retained_definitions=1,new_public_proofs=0,new_definitions=0,new_test_proofs=3,public_canary_proofs=9,named_axiom_audits=20,native_guards=11,canonical_links=12,curated_reader_links=4,new_registry_nodes=0,old_registry_IDs_URLs_preserved=10811,total_registry_nodes=10811,root_jobs=9089,Tests_jobs=9234,full_tests=466,existing_skips=7,compiled_scope_nodes=21,compiled_scope_edges=3026,actual_required_value_pairs=20)
write('accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(rows),rows=rows,all_final_fixed_inputs_rechecked=True,frozen_headers=freeze['headers'],all_original_math_bytes_retained=True,complete_definition_fixed=True,accepted_sharedmodules_oldcanary_fixed=True,Tests_original_raw_prefix=True,prior_final_history_bindings='history-binding-audit-v1.json',prior_accepted_reports_receipts_unmodified=True))
write('accepted-decision-v1.json',dict(status='accepted-with-explicit-delta',scope='Orabona v10 printed17/PDF29 Theorem2.22 iff/explicit gradient only',frozen_headers=freeze['headers'],explicit_delta=delta,qualified_public_module_sha256=sha(public),site_source_commit=integrated['site_source_commit'],stacked_base='4cf116c2ee42caa37e5a956ebbbfddfb0bc046f2',stacked_base_PR=168,final_review_receipt='final-reader-receipt-v1.json',final_review_report_sha256=final['report_sha256'],compiled_scope_graph='compiled-public-graph-v1.json',full_graph_export=False,mathematical_repairs=[],nonmathematical_repairs=integrated['failure_repairs'],site_route_repair='Original four curated links restored; all twelve canonical module/registry links retained; actual generator/checker unchanged.',main_relative_gate=integrated['main_relative_gate'],scoped_whitespace_gate=integrated['scoped_whitespace_gate'],cached_jobs_included=True,chapter_mandatory_total=None,PR_delivery_pending=True,legacy_delta_pending_PR=True,merged=False,live=False,**counts,**boundary))
write('accepted-obligations-v1.json',dict(required=[dict(name=n,statement_hash=h,state='accepted-source-Theorem2.22-refinement') for n,h in freeze['headers'].items()],full_real_germ_definition_fixed=True,legacy_migrations_before=7,legacy_remaining_pending_delivery=7,legacy_remaining_after_PR_delivery=6,exact_legacy_delta_after_delivery='ONLYOnlineSubgradientDifferentiability; zero new production math nodes and three TEST diagnostics not mathematical source gain.',chapter_total=None,future_chapters='3-16 unenumerated mandatory',main_missing_changed_Chapter1_contract_paths=9,**counts,**boundary))
pre='BanditRL.OnlineConvex.';names=[pre+n for n in freeze['headers']]+[pre+'SourceDifferentiableAt']
write('source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),additive_only=True,source_anchor='T2.22 printed17/PDF29',accepted_public_names=names,delta=delta,**counts,**boundary))
manifest='research-wiki/contribution-contracts/online-subgradient-differentiability-migration-20261007.json'
write('contribution-acceptance-overlay-v1.json',dict(manifest=manifest,manifest_sha256=sha(manifest),source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',integrated='integrated-gates-overlay-v1.json',accepted_decision='accepted-decision-v1.json',semantic_status='accepted-with-explicit-delta',earlier_candidate_pending_fields_superseded_additively=True,**boundary))
digest='Only T2.22 full iff+every-representative gradient sourcepackage accepted;11retainedproofs1fullrealgermdefinition/0newproductionmathnodes/3NEWTESTdiagnostics+6oldcanaries/20namedstandard kernel checks/11nativeguards/21selectednodes3026refs20valuepairs/12node1880readinessdistinct. '+delta+' Currentpostcomment sequentialroot9089Tests9234/fullharnessv2PASS466tests7skips afterreaderroute metadatarepair;sitecheckALL10811oldIDsURLs0newnodes/12canonicalmodulelinks4originalcuratedroutes/actualfirstviewport only/serverstopped/profilekept. Sitev1failed12curatedroutes/v2restores4 without generator/Lean weakening; allotherpreparation/test/API/rawfailures preserved. ExactPR168basecontributor/scopeddiff PASS;9otherChapter1maincontracts FAILremainmandatory. Legacy7->6ONLYcurrentmodule PENDINGrealPRdelivery; Chapter1migration/Chapter2totalnullincomplete/T2.23latermandatory/3-16unenumerated/wholeGoalACTIVE unbudgeted/mainliveunchanged/worktreeretained.'
write('memory-digest-accepted-v1.md',digest)
write('retrieval-index-accepted-v1.md','Exact11headers/fullgermdefinition/@types/pinned actualAPI/21compiledselectednodes3026refs20valuepairs/current9genuinecanaries/kernelchecks/nativeguards/CONTRACT BODY FINAL/rawhistory/qualifiedpublicSHA/applicablecurrentrootTestsfull/site12sharedlinks4curatedroute. AcceptedT2.22only, no newproduction mathematical nodes, T2.23/remainingChapter1/2 mandatory; wholeGoal ACTIVE.')
write('program-milestone-v1.json',dict(total_Goal='Chapters1-16 ACTIVE unbudgeted',bounded_milestone='Theorem2.22 iff/gradient only',legacy_remaining_before=7,legacy_remaining_pending_PR=7,legacy_remaining_after_PR=6,legacy_delta_only=['OnlineSubgradientDifferentiability'],Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,chapters3_16='unenumerated mandatory',main_updated=False,live_updated=False,**counts,**boundary))
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted','--run-id',run.name,'--attempt-id','SUBGRADIENT-DIFFERENTIABILITY-RETAINED-BODIES-V1','--statement-hash',freeze['headers']['theorem_2_22'],'--reused-declaration',pre+'theorem_2_22','--reused-declaration',pre+'theorem_2_22_gradient','--verifier-evidence',str(run/'final-reader-receipt-v1.json'),'--harness','hierarchical','--progress-class','retrieval-reuse','--reviewer-validated','--notes','Same actualcompiled retained iff/gradient accepted after distinctFINAL/currentcombinedgates/readerrepair;11retainedproof1definition/0newproductionmathnodes/3TESTdiagnostics. Sourcepackageonly/notChapter2/wholeGoal/productivityexperiment.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,accepted_decision=str(run/'accepted-decision-v1.json'),retained_proofs=11,new_proofs=0,new_test_proofs=3,merged=False,live=False,**boundary)))
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only T2.22 accepted, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_22'),'--declaration',pre+'theorem_2_22','--file',public.as_posix(),'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+pre+'theorem_2_22_gradient:compiled','--dependency','lean:'+pre+'singleton_subdifferential_hasGradientAt:compiled','--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
write('native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision_sha256=sha(run/'accepted-decision-v1.json'),actual_attempt='SUBGRADIENT-DIFFERENTIABILITY-RETAINED-BODIES-V1',frontier='accepted-frontier-v1.json',shadow='accepted-frontier-shadow-v1',legacy_delta_pending_PR=True,**boundary))
print('Only exact T2.22 sourcepackage accepted; wholeGoal ACTIVE/PRpending.')
