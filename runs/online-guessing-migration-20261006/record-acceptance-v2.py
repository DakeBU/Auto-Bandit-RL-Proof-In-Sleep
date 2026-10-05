"""Record only the reviewed guessing example and its genuine comparison refinement."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-GUESSING-MIGRATION-20261006';cache={}
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):
 key=str(p)
 if key not in cache:cache[key]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[key]
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
history_names=['runs/online-ogd-migration-20261005/historical-raw-supersession-v2.json']
history_names+=['runs/'+n+'-20261005/historical-raw-supersession-v1.json' for n in ['online-ftl-migration','online-convex-migration','online-finite-loss','online-first-order-migration','online-optimality-migration','online-expectation-migration','online-barycenter-migration','online-minorant-migration','online-jensen-migration']]
history_names.append(str(run/'historical-raw-supersession-v1.json'));snapshots={}
for name in history_names:
 for row in load(name)['rows']:
  assert sha(row['snapshot'])==row['raw_sha256'];snapshots[(row['path'],row['raw_sha256'])]=row['snapshot']
rows=[];final=None
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
 receipt=load(run/name);assert receipt['actor']['task']=='/root/source_reviewer' and receipt['verdict'] in ['accepted','accepted-with-explicit-delta']
 assert not receipt.get('mathematical_repairs',[]) and not receipt.get('required_repairs',[]) and sha(receipt['report'])==receipt['report_sha256']
 reviewed={row['path']:row['sha256'] for row in receipt['reviewed_files']}
 if name=='final-reader-receipt-v1.json':
  final=receipt
  for row in load(run/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
 for p,h in reviewed.items():
  resolved=p if sha(p)==h else snapshots[(p,h)];assert sha(resolved)==h
  rows.append(dict(receipt=name,path=p,sha256=h,resolved=resolved))
integrated=load(run/'integrated-gates-overlay-v1.json')
for label in integrated['actual_passed_gates']:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v2.json');headers=load('docs/contracts/online-guessing-migration-v1/headers-native-v2.json')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
for p in freeze['module']:
 original=run/('original-'+Path(p).name+'.txt')
 assert Path(p).read_bytes().endswith(original.read_bytes()) and tokens(Path(p).read_text(encoding='utf-8'))==tokens(original.read_text(encoding='utf-8'))
for n,row in headers.items():assert hashlib.sha256(lean_declaration_header(Path(row['file']),n).encode()).hexdigest()==freeze['headers'][n]
for p,h in freeze['canary'].items():assert sha(p)==h
actual=load(run/'public-actual-bindings-v1.json')
for p,h in actual['public_modules'].items():assert sha(p)==h
for p,h in actual['new_canary'].items():assert sha(p)==h
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
boundary=dict(source_package_accepted=True,derived_comparison_accepted=True,chapter_complete=False,goal_complete=False)
write('accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(rows),rows=rows,all_final_fixed_inputs_rechecked=True,frozen_headers=freeze['headers'],all_actual_body_and_canary_bytes_fixed=True,prior_final_history_bindings='history-binding-audit-v1.json',prior_accepted_reports_receipts_unmodified=True))
write('accepted-decision-v1.json',dict(status='accepted-with-explicit-delta',scope='One printed Orabona v10 Example2.14 plus derived actual same-zero-stream OGD versus mean comparison',source_anchor='printed15/PDF27; Chapter1 mean predictor dependency printed4/PDF16',frozen_headers=freeze['headers'],explicit_delta='Printed O(sqrtT), derived2sqrtT and fixed-initialization lower. Samezero stream/different valid fixed initializations OGD1/mean1/2; actual strict-prefix mean loss1/4, actualgap>=n/4-1/4, forall realC/naturalN existsn>N gap>C. Separate known-horizon runs, unbounded-tail existence, not equal-initialization/uniformstream/everyinit/anytime/Tendsto/minimax/Chapter4 theorem. Real[0,1] labels and produced global regularity.',retained_public_proofs=9,retained_public_definitions=1,new_public_proofs=3,new_definitions=0,public_canary_proofs=6,public_canary_definitions=2,named_axiom_audits=21,native_guards=12,new_registry_nodes=3,old_registry_IDs_URLs_preserved=10806,root_jobs=9089,Tests_jobs=9232,full_tests=466,existing_skips=7,root_Tests_execution_overlapped=False,build_boundary=integrated['execution_boundary'],site_source_commit=load(run/'registry-v2.json')['source_commit'],stacked_base='25c77a837c849eb78832673063483db5f663a73a',stacked_base_PR=163,final_review_receipt='final-reader-receipt-v1.json',final_review_report_sha256=final['report_sha256'],compiled_scope_graph='compiled-public-graph-v1.json',compiled_scope_nodes=13,compiled_scope_edges=2113,full_graph_export=False,canary_graph_export=False,mathematical_repairs=[],nonmathematical_repairs=integrated['failure_repairs'],renderer_adapter=integrated['renderer_adapter'],reader_corrections='Eight required contract/BODY corrections applied and distinctly rechecked.',main_relative_gate=integrated['main_relative_gate'],full_whitespace_gate=integrated['full_whitespace_gate'],scoped_whitespace_gate=integrated['scoped_whitespace_gate'],chapter_mandatory_total=None,PR_delivery_pending=True,merged=False,live=False,**boundary))
write('accepted-obligations-v1.json',dict(required=[dict(name=n,statement_hash=h,state='accepted-source-example-or-derived-comparison') for n,h in freeze['headers'].items()],source_printed_results=1,new_proofs=3,new_definitions=0,remaining_chapter_legacy_migrations=11,legacy_migrations_before=13,exact_accepted_legacy_delta='Only OnlineGuessingOGD and OnlineGuessingLower; three new comparison proofs counted separately, not twelve new results.',chapter_total=None,future_chapters='3-16 unenumerated mandatory',main_missing_changed_production_contract_paths=9,**boundary))
write('source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),additive_only=True,source_anchor='Example2.14 printed15/PDF27',accepted_public_names=['BanditRL.OnlineGradientDescent.'+n for n in freeze['headers']],source_printed_results=1,derived_new_comparison_proofs=3,Chapter1_dependency_is_not_chapter_acceptance=True,**boundary))
write('contribution-acceptance-overlay-v1.json',dict(manifest='research-wiki/contribution-contracts/online-guessing-migration-20261006.json',manifest_sha256=sha('research-wiki/contribution-contracts/online-guessing-migration-20261006.json'),source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',integrated='integrated-gates-overlay-v1.json',accepted_decision='accepted-decision-v1.json',semantic_status='accepted-with-explicit-delta',earlier_candidate_pending_fields_superseded_additively=True,**boundary))
write('memory-digest-accepted-v1.md','Only Example2.14 and derived true comparison accepted:9retainedproofs1domain/3newproofs0newdefinitions. Real[0,1] labels/true projection gradient/global square regularity/samecausal positive knownhorizon OGD/printed O√T vsderived2√T. Zero stream/OGDinit1/meaninit1/2, true meanloss1/4 and OGDlowern/4 produce gapn/4-1/4 and forall realC,naturalN existsn>N gap>C. Not equal-init/uniform-stream/anytime/Tendsto/minimax/Chapter4 claim. Positive n squarehorizons; n0eta totalalgebra, n1lowergap0. Whole6canaryproofs2defs/21namedstandard3-or-noneaxes/12guards/actualcompiled13nodes2113directedges/notfullcanarygraph. Sequentialroot9089Tests9232/full466tests7skips/cleanlocalsite13nodes10806oldIDsURLs3new/history/actualfirstviewportpassed. Metadata/importparser/Git-index/contributor-list failures retained, no math/test weakening; reader proof_bridge adapter samecontent. Eight reader corrections distinctly reviewed. Legacy13→11 only two retained guessing modules;3newproofs separate. Chapter1migration/Chapter2null/wholeGoalACTIVE/main/liveunchanged, PRpending/worktreeretained.')
write('retrieval-index-accepted-v1.md','Accepted source Example2.14 and actual3derived comparison proofs in current decisions/receipts/overlays. Actual meanPredict strictprefix definition produces exact1/4; actualOGD lower produces gapn/4-1/4; exists_nat_gt provides actual threshold witness. Twelve nativev2headers/nine old prooftokens/fullunitInterval unchanged, oldcanaries bytefixed/newgenuinegapcanary. All21namedaxes12guards/rootTestsfullgate/site3newnodes/oldURLs/compiled13nodes2113directreferences. RemainingChapter2 maintext/appendix/legacy obligations stillrequired, some compiled but unaudited; noChapter3proofwork, wholeGoalACTIVE.')
write('program-milestone-v1.json',dict(total_Goal='Chapters1-16 ACTIVE unbudgeted',bounded_milestone='Source Example2.14 and true OGD versus mean derived comparison accepted',legacy_remaining_before=13,legacy_remaining_after=11,exact_legacy_modules=['OnlineGuessingOGD','OnlineGuessingLower'],new_proofs=3,new_definitions=0,new_registry_nodes=3,source_printed_results=1,chapter2_mandatory_total=None,Chapter1_complete=False,chapter2_complete=False,chapters3_16='unenumerated mandatory',main_updated=False,live_updated=False,**boundary))
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted','--run-id',run.name,'--attempt-id','GUESSING-COMPARISON-V1','--statement-hash',freeze['headers']['guessing_vs_mean_unbounded'],'--new-declaration','BanditRL.OnlineGradientDescent.guessing_vs_mean_unbounded','--verifier-evidence',str(run/'final-reader-receipt-v1.json'),'--harness','hierarchical','--progress-class','terminal','--reviewer-validated','--notes','Same actual compiled comparison bundle accepted after distinct source/reader and integrated gates. One printedexample9retained3newproofs1domain. Actual terminal closed, not Chapter2/book/productivity experiment.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,accepted_decision=str(run/'accepted-decision-v1.json'),retained_proofs=9,retained_definitions=1,new_proofs=3,merged=False,live=False,**boundary)))
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; guessing example/derivedcomparison accepted, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',headers['guessing_vs_mean_unbounded']['statement'],'--declaration','BanditRL.OnlineGradientDescent.guessing_vs_mean_unbounded','--file','BanditRLProof/OnlineGuessingComparison.lean','--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineGradientDescent.guessing_vs_mean_lower:compiled','--dependency','lean:BanditRL.OnlineGradientDescent.meanPredict_zero_cumulativeLoss:compiled','--dependency','lean:BanditRL.OnlineGradientDescent.guessing_squared_horizon_lower:compiled','--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
write('native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision='accepted-decision-v1.json',accepted_decision_sha256=sha(run/'accepted-decision-v1.json'),actual_attempt='GUESSING-COMPARISON-V1',frontier='accepted-frontier-v1.json',shadow='accepted-frontier-shadow-v1',**boundary))
print('Only Example2.14 and genuine derived comparison accepted; whole Goal ACTIVE, stacked PR pending.')
