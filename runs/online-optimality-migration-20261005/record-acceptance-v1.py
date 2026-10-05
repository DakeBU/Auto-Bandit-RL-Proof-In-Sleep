"""Accept the precise retained optimality chain; the whole-book runtime Goal remains active."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-OPTIMALITY-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
cache={}
def sha(p):
 if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[p]
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
snapshots={}
for name in ['runs/online-ogd-migration-20261005/historical-raw-supersession-v2.json','runs/online-ftl-migration-20261005/historical-raw-supersession-v1.json','runs/online-convex-migration-20261005/historical-raw-supersession-v1.json','runs/online-finite-loss-20261005/historical-raw-supersession-v1.json','runs/online-first-order-migration-20261005/historical-raw-supersession-v1.json',str(run/'historical-raw-supersession-v1.json')]:
 for row in load(name)['rows']:
  assert sha(row['snapshot'])==row['raw_sha256'];snapshots[(row['path'],row['raw_sha256'])]=row['snapshot']
rows=[]
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
 r=load(run/name);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
 assert not r.get('mathematical_repairs',[]) and not r.get('required_repairs',[]) and sha(r['report'])==r['report_sha256']
 reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
 if name=='final-reader-receipt-v1.json':
  for row in load(run/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
 for p,h in reviewed.items():
  resolved=p if sha(p)==h else snapshots[(p,h)];assert sha(resolved)==h
  rows.append(dict(receipt=name,path=p,sha256=h,resolved=resolved))
for g in ['root-v1-01','Tests-v1-01','full-harness-v1-01','contributor-exact-v1-01','scoped-diff-v1-01','site-build-v1','site-check-v1','registry-v1-01','browser-v1-01','history-bindings-v1-01','candidate-frontier-shadow-v1']:
 assert load(run/(g+'-exit.json'))['exit_code']==0,g
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineConvexOptimality.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexOptimality.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
write('accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(rows),rows=rows,all_final_fixed_inputs_rechecked=True,frozen_headers=freeze['headers'],all_code_tokens_and_canary_bytes_unchanged=True,
 prior_final_history_bindings='history-binding-audit-v1.json',prior_accepted_reports_receipts_unmodified=True))
write('accepted-decision-v1.json',dict(status='accepted-with-explicit-delta',scope='four retained optimality proofs only',source_terminal='BanditRL.OnlineConvex.theorem_2_8',mandatory_unnumbered_consequence='BanditRL.OnlineConvex.interior_min_iff_gradient_zero',
 explicit_library_helpers=['minOn_real_iff_gradient','minOn_finitePart_iff'],source='Orabona v10 printed11/PDF23',frozen_headers=freeze['headers'],
 explicit_delta='Weaker convexity only on V yields stronger theorem; canonical finite/open-neighborhood derivative, complete inner-product generality. No equivalence of premise sets.',
 retained_public_proofs=4,new_public_proofs=0,definitions=0,public_canary_proofs=8,named_axiom_audits=13,native_guards=4,new_registry_nodes=0,old_registry_IDs_URLs_preserved=10806,
 root_jobs=9088,Tests_jobs=9230,full_tests=466,existing_skips=7,site_source_commit=load(run/'registry-v1.json')['source_commit'],stacked_base='c9b47c8ba79a234d0dfa6e8ef5643a43677dd33a',stacked_base_PR=158,
 final_review_receipt='final-reader-receipt-v1.json',final_review_report_sha256=r['report_sha256'],compiled_scope_graph='compiled-scoped-graph-v1.json',full_graph_export=False,canary_graph_export=False,
 main_relative_gate='FAIL14legacyproductioncontracts',full_whitespace_gate='FAILexactrawlogs',scoped_whitespace_gate='PASSenumeratedrawexceptions',chapter_mandatory_total=None,chapter_complete=False,goal_complete=False,PR_delivery_pending=True,merged=False,live=False))
write('accepted-obligations-v1.json',dict(required=[dict(name=n,statement_hash=h,state='accepted-scoped-retained') for n,h in freeze['headers'].items()],source_terminal_unnumbered_consequence_two_helpers_reviewed=True,
 new_proofs=0,remaining_chapter_legacy_migrations=17,legacy_migrations_before=18,exact_accepted_legacy_delta='OnlineConvexOptimality only; mathematical proof count unchanged',chapter_total=None,chapter_complete=False,goal_complete=False,
 future_chapters='3-16 unenumerated mandatory',main_missing_changed_production_contract_paths=14))
write('source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),additive_only=True,
 source_anchor='Theorem2.8 and following mandatory unnumbered interior consequence, printed11/PDF23',accepted_public_names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']],
 delta='Retained criterion/interior consequence/two libraryhelpers; weakerConvexOnV premise/canonicalfiniteU/Hilbert generality explicit.',chapter_complete=False,goal_complete=False))
write('contribution-acceptance-overlay-v1.json',dict(manifest='research-wiki/contribution-contracts/online-optimality-migration-20261005.json',manifest_sha256=sha('research-wiki/contribution-contracts/online-optimality-migration-20261005.json'),
 source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',integrated='integrated-gates-overlay-v1.json',accepted_decision='accepted-decision-v1.json',semantic_status='accepted-with-explicit-delta',
 earlier_candidate_pending_fields_superseded_additively=True,chapter_complete=False,goal_complete=False))
write('memory-digest-accepted-v1.md','Only4retainedoptimality proofs/sourcecriterion+mandatoryinteriorzero+2helpers accepted, no newproofcode/definitions/nodes. WeakerConvexOnV premise givesstrongertheorem, no equivalence/ConvexU/globaloutsideUconditions. CanonicalfiniteUembedding/differentiability/IsMinOnmembership separate; boundarygradient1 versus ambientinteriorquadraticzero meaningful.13namedaxioms4guards/root9088Tests9230full466tests7skips/exactstacked4production1manifest/cleanlocal site4nodes10806oldIDsURLs/actualfirstviewport/allpriorrawsnapshotbindings passed. Nativegates distinct role/file conventions. Auxiliarylabeloriginal exactly reconstructed afterchange/hashmatchedpreparation, timingexplicit/notrawpre-capture. Legacy18→17 module migrationonly, main-relative14gaps/Chapter2totalnull/wholeGoalactive; PRpending/unmerged/liveunchanged/worktreeretained.')
write('retrieval-index-accepted-v1.md','Accepteddecision/binding/obligations/overlays here; actualnative4headers andsourcecontext inonline-optimality-migration-v1. PublicOnlineConvexOptimality and unchangedcanary8proofs1definition,13axioms4guards; current scopedcompiled4node510edges/5projectvaluepairs, notfull/canaryexport. Distinctcontract/body/finalreader receipts andsnapshotchains; same sharedregistry/sourcequalifiedOnlineBookroute. Next dependency-ready source spines: signed expectation/finite-dimensional convex barycenter/Jensen, each own sourcecontract required. Chapter/book Goal remainsactive.')
write('program-milestone-v1.json',dict(total_Goal='Chapters1-16 active unbudgeted',bounded_milestone='Theorem2.8 and mandatory unnumbered interior consequence retained migration accepted',legacy_remaining_before=18,legacy_remaining_after=17,new_proofs=0,new_registry_nodes=0,
 chapter2_mandatory_total=None,chapter2_complete=False,chapters3_16='unenumerated mandatory',goal_complete=False,main_updated=False,live_updated=False))
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted','--run-id',run.name,
 '--attempt-id','OPTIMALITY-RETAINED-BODIES-V1','--statement-hash',freeze['headers']['theorem_2_8'],'--reused-declaration','BanditRL.OnlineConvex.theorem_2_8','--verifier-evidence',str(run/'final-reader-receipt-v1.json'),
 '--harness','hierarchical','--progress-class','retrieval-reuse','--reviewer-validated','--notes','Same named actual compiled reuse bundle accepted after separate finalsource/reader and integratedgates;4retainedcontracts/no newproofs, no chapter/bookcompletion/timingexperimentclaim.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,accepted_decision=str(run/'accepted-decision-v1.json'),retained_proofs=4,new_proofs=0,chapter_complete=False,goal_complete=False,merged=False,live=False)))
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only retained optimality chain accepted, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_8'),'--declaration','BanditRL.OnlineConvex.theorem_2_8','--file',public.as_posix(),'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineConvex.minOn_real_iff_gradient:compiled','--dependency','lean:BanditRL.OnlineConvex.minOn_finitePart_iff:compiled','--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
write('native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision='accepted-decision-v1.json',accepted_decision_sha256=sha(run/'accepted-decision-v1.json'),actual_attempt='OPTIMALITY-RETAINED-BODIES-V1',
 frontier='accepted-frontier-v1.json',shadow='accepted-frontier-shadow-v1',chapter_complete=False,goal_complete=False))
print('Scoped4retainedoptimality acceptance recorded; whole realGoalACTIVE, stackedPRdelivery pending.')
