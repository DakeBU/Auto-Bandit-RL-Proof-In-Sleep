"""Accept only T2.23 after distinct FINAL and actual integrated gates."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007';pre='BanditRL.OnlineConvex.'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));cache={}
def sha(p):
 k=str(p)
 if k not in cache:cache[k]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[k]
def write(n,x):
 p=run/n;assert not p.exists(),p
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
history=load(run/'history-binding-audit-v2.json');snapshots={(r['path'],r['raw_sha256']):r['resolved_raw_file'] for r in history['rows']}
rows=[];final=None
for n in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
 r=load(run/n);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
 assert not r.get('mathematical_repairs',[]) and not r.get('required_mathematical_repairs',[]) and not r.get('required_repairs',[]) and sha(r['report'])==r['report_sha256']
 reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
 if n=='final-reader-receipt-v1.json':
  final=r
  for row in load(run/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
 for p,h in reviewed.items():
  resolved=p if sha(p)==h else snapshots[(p,h)];assert sha(resolved)==h,p
  rows.append(dict(receipt=n,path=p,sha256=h,resolved=resolved))
integrated=load(run/'integrated-gates-overlay-v1.json')
for n in integrated['actual_passed_gates']:assert load(run/(n+'-exit.json'))['exit_code']==0,n
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientSum.lean')
assert public.read_bytes().endswith((run/'original-OnlineSubgradientSum.lean.txt').read_bytes())
assert sha(public)==load(run/'public-comment-qualification-v1.json')['qualified_sha256']
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for group in ['fixed_shared_files','whole_old_canary']:
 for p,h in freeze[group].items():assert sha(p)==h,p
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
boundary=dict(source_package_accepted=True,chapter_complete=False,goal_complete=False)
delta='One printed T2.23/TWO branches. Inclusion only proper components/arbitraryFintype/allqueriedx; no convexity/commonfinite/queryfinite. Generic global S extends printed proper-function Definition2.20: disjoint proper domains yield identicallytop aggregate with ALLvectors supporting and EMPTYMinkowski side; proper components not aggregateproper. NoBottom legitimizes ordinary versus top-dominant upperAdd, mixed infinities differ. Equality positiveFin(n+1), ALLproper/convex/CLOSED, independentz in lastDOMAIN and allOTHER AMBIENTinteriors; lastboundary and singleton qualificationvacuity permitted, otherregularity retained. Main derives aggregateproper/queryfinite/componentfinite; strongerbinary interface suppliesqueryfinite/dropsclosed. Actual epigraph image/contact/nonzero separation/strictnegativec/Riesz complementarysupports/prefixinteriorproper/recursiveequality/Fin.snoc vectorfamily, not decompositionoracle. Six vectorproofsfiniteDrealinner/derivedcomplete/zeroD;3scalarnoE/fullMnoFD; REALepigraph andsublevelclosedness. Empty-index inclusion-only libraryextension; REALsingleton emptyinterior notzeroDuniversal. No algorithm/regret/external Cor16.50 rebuild.'
counts=dict(source_numbered_anchors=1,source_branches=2,retained_public_proofs=9,retained_definitions=1,new_public_proofs=0,new_definitions=0,new_test_proofs=0,public_canary_proofs=20,public_canary_definitions=3,named_axiom_audits=29,native_guards=9,canonical_links=10,curated_reader_links=4,new_registry_nodes=0,old_registry_IDs_URLs_preserved=10811,total_registry_nodes=10811,root_jobs=9089,Tests_jobs=9234,full_tests=466,existing_skips=7,compiled_scope_nodes=33,compiled_scope_edges=2844,actual_required_value_pairs=22)
write('accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(rows),rows=rows,all_final_fixed_inputs_rechecked=True,frozen_headers=freeze['headers'],all_original_math_bytes_retained=True,complete_definition_fixed=True,whole_old_canary_shared_modules_roots_pins_fixed=True,prior_final_history_bindings='history-binding-audit-v2.json',prior_accepted_reports_receipts_unmodified=True))
write('accepted-decision-v1.json',dict(status='accepted-with-explicit-delta',scope='Orabona v10 printed17-18/PDF29-30 Theorem2.23 bothbranches only',frozen_headers=freeze['headers'],explicit_delta=delta,qualified_public_module_sha256=sha(public),site_source_commit=integrated['site_source_commit'],stacked_base='52c24a9971a5d7953a129227b61384061ea3493e',stacked_base_PR=169,final_review_receipt='final-reader-receipt-v1.json',final_review_report_sha256=final['report_sha256'],compiled_scope_graph='compiled-public-graph-v1.json',full_graph_export=False,mathematical_repairs=[],nonmathematical_repairs=integrated['failure_repairs'],main_relative_gate=integrated['main_relative_gate'],scoped_whitespace_gate=integrated['scoped_whitespace_gate'],cached_jobs_included=True,chapter_mandatory_total=None,PR_delivery_pending=True,legacy_delta_pending_PR=True,merged=False,live=False,**counts,**boundary))
write('accepted-obligations-v1.json',dict(required=[dict(name=n,statement_hash=h,state='accepted-T2.23-source-refinement') for n,h in freeze['headers'].items()],full_M_definition_fixed=True,legacy_migrations_before=6,legacy_remaining_pending_delivery=6,legacy_remaining_after_PR_delivery=5,exact_legacy_delta_after_delivery='ONLYOnlineSubgradientSum; zero new productionmath/TESTs, not nine new source results.',chapter_total=None,future_chapters='3-16 unenumerated mandatory',main_missing_changed_Chapter1_contract_paths=9,**counts,**boundary))
names=[pre+n for n in freeze['headers']]+[pre+'SourceSubgradientSum']
write('source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),additive_only=True,source_anchor='ONE T2.23 printed17-18/PDF29-30/TWObranches',accepted_public_names=names,delta=delta,**counts,**boundary))
manifest='research-wiki/contribution-contracts/online-subgradient-sum-migration-20261007.json'
write('contribution-acceptance-overlay-v1.json',dict(manifest=manifest,manifest_sha256=sha(manifest),source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',integrated='integrated-gates-overlay-v1.json',accepted_decision='accepted-decision-v1.json',semantic_status='accepted-with-explicit-delta',earlier_candidate_pending_fields_superseded_additively=True,**boundary))
digest='T2.23 sourcepackage ONLY accepted;9retainedproofs/fullM/0newmath or TESTs/whole20canaryproofs3defs/29kernelchecks/9guards/33selectednodes2844refs22pairs/10node1146readinessseparate. '+delta+' Current postcomment sequentialroot9089Tests9234/full466tests7skips/sitecheckALL10811IDsURLs0newnodes/ten canonical links4originalroutes/actualfirstviewport/serverstopped/profilepreserved. Preparationfailures preserved, no mathematical weakening. ExactPR169base contributor/scopedwhitespacePASS/nineOTHERChapter1maincontractgapsFAILmandatory. Legacy6->5ONLYSum PENDING realPR; nextEx2.24+remainingChapter1/2appendixmandatory, Chapter2totalnullincomplete/3-16unenumerated/wholeGoalACTIVE/unbudgeted, mainliveunchanged/worktreeretained.'
write('memory-digest-accepted-v1.md',digest)
write('retrieval-index-accepted-v1.md','Actual9headers/fullM/@types/pinned19APIs/33selectednodes2844refs22valuepairs/whole20actualcanaries3defs/29kernelchecks9nativeguards/CONTRACT BODY FINAL/rawhistory/qualifiedsourceSHA/currentapplicablecombinedgates/10sharedlinks4curatedroutes. AcceptedONLY T2.23bothbranches; zero newmath, nextEx2.24 mandatory/wholeGoal ACTIVE.')
write('program-milestone-v1.json',dict(total_Goal='Chapters1-16 ACTIVE unbudgeted',bounded_milestone='ONE T2.23 bothbranches only',legacy_remaining_before=6,legacy_remaining_pending_PR=6,legacy_remaining_after_PR=5,legacy_delta_only=['OnlineSubgradientSum'],Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,chapters3_16='unenumerated mandatory',main_updated=False,live_updated=False,**counts,**boundary))
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted','--run-id',run.name,'--attempt-id','SUBGRADIENT-SUM-RETAINED-BODIES-V1','--statement-hash',freeze['headers']['theorem_2_23_equality'],'--reused-declaration',pre+'theorem_2_23_inclusion','--reused-declaration',pre+'theorem_2_23_equality','--verifier-evidence',str(run/'final-reader-receipt-v1.json'),'--harness','hierarchical','--progress-class','retrieval-reuse','--reviewer-validated','--notes','Same actualcompiled retained sum producer accepted after distinctFINAL/currentcombinedgates.9retainedproof/fullM/0newmath or TESTs. T2.23sourcepackageonly/notChapter2/book/productivityexperiment.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,accepted_decision=str(run/'accepted-decision-v1.json'),retained_proofs=9,new_proofs=0,new_test_proofs=0,merged=False,live=False,**boundary)))
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only T2.23accepted, chapter/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_23_equality'),'--declaration',pre+'theorem_2_23_equality','--file',public.as_posix(),'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+pre+'theorem_2_23_inclusion:compiled','--dependency','lean:'+pre+'binary_subgradient_decomposition:compiled','--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
write('native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision_sha256=sha(run/'accepted-decision-v1.json'),actual_attempt='SUBGRADIENT-SUM-RETAINED-BODIES-V1',frontier='accepted-frontier-v1.json',shadow='accepted-frontier-shadow-v1',legacy_delta_pending_PR=True,**boundary))
print('ONLY T2.23 sourcepackage accepted; whole Goal ACTIVE/PR pending.')
