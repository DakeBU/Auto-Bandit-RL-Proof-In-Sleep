"""Accept only reviewed retained Theorem2.7 chain; never complete the runtime book Goal."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-FIRST-ORDER-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
snapshots={}
for name in ['runs/online-ogd-migration-20261005/historical-raw-supersession-v2.json','runs/online-ftl-migration-20261005/historical-raw-supersession-v1.json','runs/online-convex-migration-20261005/historical-raw-supersession-v1.json','runs/online-finite-loss-20261005/historical-raw-supersession-v1.json',str(run/'historical-raw-supersession-v1.json')]:
 for row in load(name)['rows']:
  assert sha(row['snapshot'])==row['raw_sha256'];snapshots[(row['path'],row['raw_sha256'])]=row['snapshot']
rows=[]
for n in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
 r=load(run/n);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
 assert not r.get('mathematical_repairs',[]) and not r.get('required_repairs',[])
 assert sha(r['report'])==r['report_sha256']
 reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
 if n=='final-reader-receipt-v1.json':
  for row in load(run/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
 for p,h in reviewed.items():
  resolved=p if sha(p)==h else snapshots[(p,h)];assert sha(resolved)==h
  rows.append(dict(receipt=n,path=p,sha256=h,resolved=resolved))
for g in ['root-v1-01','Tests-v1-01','full-harness-v1-01','contributor-exact-v1-01','scoped-diff-v1-01','site-build-v1','site-check-v1','registry-v1-01','browser-v1-01','history-bindings-v1-01','candidate-frontier-shadow-v1']:
 assert load(run/(g+'-exit.json'))['exit_code']==0,g
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineConvexFirstOrder.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexFirstOrder.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
write('accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(rows),rows=rows,all_final_fixed_inputs_rechecked=True,
 frozen_headers=freeze['headers'],all_code_tokens_and_canary_bytes_unchanged=True,prior_final_history_bindings='history-binding-audit-v1.json',prior_accepted_reports_receipts_unmodified=True))
write('accepted-decision-v1.json',dict(status='accepted-with-explicit-delta',scope='three retained first-order proofs only',
 source_terminal='BanditRL.OnlineConvex.theorem_2_7',explicit_library_helpers=['finitePart_eventually','convex_gradient_lower_bound'],
 source='Orabona v10 Theorem2.7 printed11/PDF23',frozen_headers=freeze['headers'],retained_public_proofs=3,new_public_proofs=0,definitions=0,
 public_canary_proofs=8,named_axiom_audits=12,native_guards=3,new_registry_nodes=0,old_registry_IDs_URLs_preserved=10806,
 root_jobs=9088,Tests_jobs=9230,full_tests=466,existing_skips=7,source_compatible_OGD_vs_stronger_historical_RegularLoss_visible=True,
 site_source_commit=load(run/'registry-v1.json')['source_commit'],stacked_base='a6607d8213860619965c7018e4dd2effff58422a',stacked_base_PR=157,
 final_review_receipt='final-reader-receipt-v1.json',final_review_report_sha256=r['report_sha256'],
 compiled_scope_graph='compiled-scoped-graph-v1.json',full_graph_export=False,canary_graph_export=False,
 main_relative_gate='FAIL15legacyproductioncontracts',full_whitespace_gate='FAILexactrawlogs',scoped_whitespace_gate='PASSenumeratedrawexceptions',
 chapter_mandatory_total=None,chapter_complete=False,goal_complete=False,PR_delivery_pending=True,merged=False,live=False))
write('accepted-obligations-v1.json',dict(required=[dict(name=n,statement_hash=h,state='accepted-scoped-retained') for n,h in freeze['headers'].items()],
 source_terminal_and_two_library_helpers_reviewed=True,new_proofs=0,remaining_chapter_legacy_migrations=18,legacy_migrations_before=19,
 exact_accepted_legacy_delta='OnlineConvexFirstOrder only; mathematical proof count unchanged',chapter_total=None,chapter_complete=False,goal_complete=False,
 future_chapters='3-16 unenumerated mandatory',main_missing_changed_production_contract_paths=15))
write('source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),additive_only=True,
 source_anchor='Theorem2.7 printed11/PDF23',accepted_public_names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']],
 delta='Retained terminal and two library helpers; complete inner-product generality, canonical locally faithful derivative interpretation explicit.',chapter_complete=False,goal_complete=False))
write('contribution-acceptance-overlay-v1.json',dict(manifest='research-wiki/contribution-contracts/online-first-order-migration-20261005.json',manifest_sha256=sha('research-wiki/contribution-contracts/online-first-order-migration-20261005.json'),
 source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',integrated='integrated-gates-overlay-v1.json',
 accepted_decision='accepted-decision-v1.json',semantic_status='accepted-with-explicit-delta',earlier_candidate_pending_fields_superseded_additively=True,chapter_complete=False,goal_complete=False))
write('memory-digest-accepted-v1.md','Theorem2.7 plus local representation/real ConvexOn helpers distinctly accepted with explicit Hilbert-space/canonical local derivative qualifications. Three retained bodies/no definitions/newproofs/nodes,12namedaxioms/3guards/meaningful byte-unchanged canary. Fresh root9088/Tests9230/full466tests7existing skips; exact stacked4production1manifest pass; clean site3canonical nodes and10806oldIDsURLs preserved; actualfirstviewport observed, lowerHTML audited. Source/comment/reader snapshot chains preserve4190priorrawbindings. Historical RegularLoss stronger than separately source-compatible OGD adapter, no equivalence claim. Legacy19→18 bounded module migration only; main-relative15gaps, Chapter2totalnull/incomplete, whole Chapters1-16 Goalactive. PRpending/unmerged/live unchanged; no retirement/model upgrade.')
write('retrieval-index-accepted-v1.md','Current source/header contracts online-first-order-migration-v1. Immutable accepted decision/binding/obligations/additiveoverlays and distinct contract/body/finalreader receipts. Public3retained bodies/unchanged canary/12namedaxioms/3guards/current scoped actualgraph3nodes416edges. Same canonical shared registry/URLs/OnlineBook. Next dependency-ready source/migration: first-order optimality Theorem2.8 and interior-zero consequence, exactsource review still required. No blanket source count/chapter/book completion.')
write('program-milestone-v1.json',dict(total_Goal='Chapters1-16 active unbudgeted',bounded_milestone='Theorem2.7 retained semantic migration accepted',legacy_remaining_before=19,legacy_remaining_after=18,
 new_proofs=0,new_registry_nodes=0,chapter2_mandatory_total=None,chapter2_complete=False,chapters3_16='unenumerated mandatory',goal_complete=False,main_updated=False,live_updated=False))
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted','--run-id',run.name,
 '--attempt-id','FIRST-ORDER-RETAINED-BODIES-V1','--statement-hash',freeze['headers']['theorem_2_7'],'--reused-declaration','BanditRL.OnlineConvex.theorem_2_7',
 '--verifier-evidence',str(run/'final-reader-receipt-v1.json'),'--harness','hierarchical','--progress-class','retrieval-reuse','--reviewer-validated',
 '--notes','Same named actually compiled reuse attempt accepted after distinct final source/reader and integrated gates; three retained contracts, zero new proofs, Chapter2/book incomplete. No timing/productivity experiment claim.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,accepted_decision=str(run/'accepted-decision-v1.json'),retained_proofs=3,new_proofs=0,chapter_complete=False,goal_complete=False,merged=False,live=False)))
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only retained Theorem2.7 chain accepted, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_7'),'--declaration','BanditRL.OnlineConvex.theorem_2_7','--file',public.as_posix(),'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineConvex.finitePart_eventually:compiled','--dependency','lean:BanditRL.OnlineConvex.convex_gradient_lower_bound:compiled','--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
write('native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision='accepted-decision-v1.json',accepted_decision_sha256=sha(run/'accepted-decision-v1.json'),
 actual_attempt='FIRST-ORDER-RETAINED-BODIES-V1',frontier='accepted-frontier-v1.json',shadow='accepted-frontier-shadow-v1',chapter_complete=False,goal_complete=False))
print('Scoped retained first-order migration accepted; whole real Goal remains ACTIVE; stacked PR delivery pending.')
